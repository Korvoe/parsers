from __future__ import print_function
from GoLexer import GoLexer
from antlr4 import *

class GoParserBase(Parser):
    def __init__(self, input, output):
        super(GoParserBase, self).__init__(input)

    def lineTerminatorAhead(self):
        possibleIndexEosToken = self.getCurrentToken().tokenIndex - 1
        if possibleIndexEosToken == -1:
            return True
        ahead = self._input.get(possibleIndexEosToken)
        if ahead.channel != Lexer.HIDDEN:
            return False
        if ahead.type == GoLexer.TERMINATOR:
            return True
        if ahead.type == GoLexer.WS:
            possibleIndexEosToken = self.getCurrentToken().tokenIndex - 2
            ahead = self._input.get(possibleIndexEosToken)
        text = ahead._text
        type_ = ahead.type
        return (type_ == GoLexer.COMMENT and (text.contains("\r") or text.contains("\n"))) or (type_ == GoLexer.TERMINATOR)

    def noTerminatorBetween(self, tokenOffset):
        stream = self._input
        tokens = stream.getHiddenTokensToLeft(stream.LT(tokenOffset).tokenIndex)
        if tokens == None:
            return True
        for token in tokens:
            if token._text:
                if token._text.contains("\n"):
                    return False
        return True

    def noTerminatorAfterParams(self, tokenOffset):
        stream = self._input
        leftParams = 1
        rightParams = 0
        valueType = int()
        if stream.LT(tokenOffset).type == GoLexer.L_PAREN:
            while leftParams != rightParams:
                tokenOffset += 1
                valueType = stream.LT(tokenOffset).type
                if valueType == GoLexer.L_PAREN:
                    leftParams += 1
                elif valueType == GoLexer.R_PAREN:
                    rightParams += 1
            tokenOffset += 1
            return self.noTerminatorBetween(tokenOffset)
        return True

    def checkPreviousTokenText(self, text):
        stream = self._input
        prevTokenText = stream.LT(1)._text
        if prevTokenText == None:
            return False
        return prevTokenText == text
