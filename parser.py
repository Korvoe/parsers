import os
import sys
import subprocess
import json
import re
import regex
import pcre
from antlr4 import *
from JavaLexer import JavaLexer
from JavaParser import JavaParser
from JavaParserListener import JavaParserListener
from JavaScriptParser import JavaScriptParser
from JavaScriptLexer import JavaScriptLexer
from JavaScriptParserListener import JavaScriptParserListener
from Python3Parser import Python3Parser
from Python3Lexer import Python3Lexer
from Python3Listener import Python3Listener
from GoParser import GoParser
from GoLexer import GoLexer
from GoParserListener import GoParserListener
import platform
import multiprocessing
import get_cpu_count
from hashlib import md5
import time
import textwrap

global javaCallCommand

class function:
    parentFile = None  # Absolute file which has the function
    parentNumLoc = None  # Number of LoC of the parent file
    name = None  # Name of the function
    lines = None  # Tuple (lineFrom, lineTo) that indicates the LoC of function
    funcId = None  # n, indicating n-th function in the file
    parameterList = []  # list of parameter variables
    variableList = []  # list of local variables
    dataTypeList = []  # list of data types, including user-defined types
    funcCalleeList = []  # list of called functions' names
    funcBody = None

    def __init__(self, fileName):
        self.parentFile = fileName
        self.parameterList = []
        self.variableList = []
        self.dataTypeList = []
        self.funcCalleeList = []

    def removeListDup(self):
        # for best performance, must execute this method
        # for every instance before applying the abstraction.
        self.parameterList = list(set(self.parameterList))
        self.variableList = list(set(self.variableList))
        self.dataTypeList = list(set(self.dataTypeList))
        self.funcCalleeList = list(set(self.funcCalleeList))

def normalize(string):
    # Code for normalizing the input string.
    # LF and TAB literals, curly braces, and spaces are removed,
    # and all characters are lowercased.
    return ''.join(string.replace('\n', '').replace('\r', '').replace('\t', '').replace('{', '').replace('}', '').split(' ')).lower()

def removeComment(string):
    # Code for removing C/C++ style comments.  (Imported from ReDeBug.)
    c_regex = re.compile(r'(?P<comment>//.*?$|[{}]+)|(?P<multilinecomment>/\*.*?\*/)|(?P<noncomment>\'(\\.|[^\\\'])*\'|"(\\.|[^\\"])*"|.[^/\'"]*)',
        re.DOTALL | re.MULTILINE)
    return ''.join([c.group('noncomment') for c in c_regex.finditer(string) if c.group('noncomment')])

def new_abstract(instance, level):
    # Applies abstraction on the function instance,
    # and then returns a tuple consisting of the original body and abstracted
    # body.
    originalFunctionBody = instance.funcBody
    originalFunctionBody = removeComment(originalFunctionBody)

    if int(level) >= 0:  # No abstraction.
        abstractBody = originalFunctionBody

    if int(level) >= 1:  # PARAM
        parameterList = instance.parameterList
        for param in parameterList:
            if len(param) == 0:
                continue
            try:
                paramPattern = re.compile("(^|\W)" + param + "(\W)")
                abstractBody = paramPattern.sub("\g<1>FPARAM\g<2>", abstractBody)
            except:
                pass

    if int(level) >= 2:  # DTYPE
        dataTypeList = instance.dataTypeList
        for dtype in dataTypeList:
            if len(dtype) == 0:
                continue
            try:
                dtypePattern = re.compile("(^|\W)" + dtype + "(\W)")
                abstractBody = dtypePattern.sub("\g<1>DTYPE\g<2>", abstractBody)
            except:
                pass

    if int(level) >= 3:  # LVAR
        variableList = instance.variableList
        for lvar in variableList:
            if len(lvar) == 0:
                continue
            try:
                lvarPattern = re.compile("(^|\W)" + lvar + "(\W)")
                abstractBody = lvarPattern.sub("\g<1>LVAR\g<2>", abstractBody)
            except:
                pass

    if int(level) >= 4:  # FUNCCALL
        funcCalleeList = instance.funcCalleeList
        for fcall in funcCalleeList:
            if len(fcall) == 0:
                continue
            try:
                fcallPattern = re.compile("(^|\W)" + fcall + "(\W)")
                abstractBody = fcallPattern.sub("\g<1>METHODCALL\g<2>", abstractBody)
            except:
                pass

    return (originalFunctionBody, abstractBody)

def abstract(instance, level):
    # Applies abstraction on the function instance,
    # and then returns a tuple consisting of the original body and abstracted
    # body.
    originalFunctionBody = instance.funcBody
    originalFunctionBody = removeComment(originalFunctionBody)

    if int(level) >= 0:  # No abstraction.
        abstractBody = originalFunctionBody

    if int(level) >= 1:  # PARAM
        parameterList = instance.parameterList
        for param in parameterList:
            if len(param) == 0:
                continue
            try:
                paramPattern = re.compile("(^|\W)" + param + "(\W)")
                abstractBody = paramPattern.sub("\g<1>FPARAM\g<2>", abstractBody)
            except:
                pass

    if int(level) >= 2:  # DTYPE
        dataTypeList = instance.dataTypeList
        for dtype in dataTypeList:
            if len(dtype) == 0:
                continue
            try:
                dtypePattern = re.compile("(^|\W)" + dtype + "(\W)")
                abstractBody = dtypePattern.sub("\g<1>DTYPE\g<2>", abstractBody)
            except:
                pass

    if int(level) >= 3:  # LVAR
        variableList = instance.variableList
        for lvar in variableList:
            if len(lvar) == 0:
                continue
            try:
                lvarPattern = re.compile("(^|\W)" + lvar + "(\W)")
                abstractBody = lvarPattern.sub("\g<1>LVAR\g<2>", abstractBody)
            except:
                pass

    if int(level) >= 4:  # FUNCCALL
        funcCalleeList = instance.funcCalleeList
        for fcall in funcCalleeList:
            if len(fcall) == 0:
                continue
            try:
                fcallPattern = re.compile("(^|\W)" + fcall + "(\W)")
                abstractBody = fcallPattern.sub("\g<1>FUNCCALL\g<2>", abstractBody)
            except:
                pass

    return (originalFunctionBody, abstractBody)

#Original shallow C\C++ code parser using Antlr
def parse_shallow(files):
    javaCallCommand = "java -Xmx1024m -jar FuncParser-opt.jar " + files + " 1"
    global delimiter
    delimiter = "\r\0?\r?\0\r"
    # this parses function definition plus body.
    functionInstanceList = []

    try:
        astString = subprocess.check_output(javaCallCommand, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    funcList = astString.split(delimiter)
    for func in funcList[1:]:
        functionInstance = function(files)

        elemsList = func.split('\n')[1:-1]
        # print elemsList
        if len(elemsList) > 9:
            functionInstance.parentNumLoc = int(elemsList[1])
            functionInstance.name = elemsList[2]
            functionInstance.lines = (int(elemsList[3].split('\t')[0]), int(elemsList[3].split('\t')[1]))
            functionInstance.funcId = int(elemsList[4])
            functionInstance.funcBody = '\n'.join(elemsList[9:])
            functionInstanceList.append(functionInstance)

    return functionInstanceList

#Original deep C/C++ code parser using Antlr
def parse_deep(files):
    javaCallCommand = "java -Xmx1024m -jar FuncParser-opt.jar " + files + " 1"
    global delimiter
    delimiter = "\r\0?\r?\0\r"
    # this parses function definition plus body.
    functionInstanceList = []

    try:
        astString = subprocess.check_output(javaCallCommand, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    funcList = astString.split(delimiter)
    for func in funcList[1:]:
        functionInstance = function(files)

        elemsList = func.split('\n')[1:-1]
        # print elemsList
        if len(elemsList) > 9:
            functionInstance.parentNumLoc = int(elemsList[1])
            functionInstance.name = elemsList[2]
            functionInstance.lines = (int(elemsList[3].split('\t')[0]), int(elemsList[3].split('\t')[1]))
            functionInstance.funcId = int(elemsList[4])
            functionInstance.parameterList = elemsList[5].rstrip().split('\t')
            functionInstance.variableList = elemsList[6].rstrip().split('\t')
            functionInstance.dataTypeList = elemsList[7].rstrip().split('\t')
            functionInstance.funcCalleeList = elemsList[8].rstrip().split('\t')
            functionInstance.funcBody = '\n'.join(elemsList[9:])
            print(functionInstance.funcBody)
            print("funccalls: " + str(functionInstance.funcCalleeList))
            print("variables: " + str(functionInstance.variableList))
            print("parameters: " + str(functionInstance.parameterList))
            print("data types: " + str(functionInstance.dataTypeList))
            functionInstanceList.append(functionInstance)

    return functionInstanceList

#Shallow JAVA code parser using Universal-Ctags
def parse_java_shallow(file):
    Command = "ctags -f - --kinds-java=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    methodList = astString.split('\n')
    method = re.compile(r'(method)')
    number = re.compile(r'(\d+)')
    funcBody = re.compile(r'{([\S\s]*)}')
    string = ""
    funcId = 1
    methodInstanceList = []

    for i in methodList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        methodInstance = function(file)
        methodInstance.funcBody = ''

        if i != '' and method.match(elemList[3]) and len(elemList) >= 6:
            methodInstance.name = elemList[0]
            methodInstance.parentFile = elemList[1]
            methodInstance.lines = (int(number.search(elemList[4]).group(0)),
                                    int(number.search(elemList[5]).group(0)))
            methodInstance.parentNumLoc = len(lines)
            string = ""
            string = string.join(lines[methodInstance.lines[0]-1:methodInstance.lines[1]])
            if funcBody.search(string):
                methodInstance.funcBody = methodInstance.funcBody + funcBody.search(string).group(1)
            else:
                methodInstance.funcBody = " "
            methodInstance.funcId = funcId
            funcId+=1
            print(methodInstance.funcBody)
            methodInstanceList.append(methodInstance)

    return methodInstanceList

#Deep JAVA code parser using Universal-Ctags
def parse_java_deep(file):
    Command = "ctags -f - --kinds-java=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    methodList = astString.split('\n')
    method = re.compile(r'(method)')
    number = re.compile(r'(\d+)')
    funcBody = re.compile(r'{([\S\s]*)}')
    string = ""
    funcId = 1
    methodInstanceList = []

    for i in methodList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        methodInstance = function(file)
        methodInstance.funcBody = ''

        if i != '' and method.match(elemList[3]) and len(elemList) >= 6:
            methodInstance.name = elemList[0]
            methodInstance.parentFile = elemList[1]
            methodInstance.lines = (int(number.search(elemList[4]).group(0)),
                                    int(number.search(elemList[5]).group(0)))
            methodInstance.parentNumLoc = len(lines)
            string = ""
            string = string.join(lines[methodInstance.lines[0]-1:methodInstance.lines[1]])
            if funcBody.search(string):
                methodInstance.funcBody = methodInstance.funcBody + funcBody.search(string).group(0)
                lexer = JavaLexer(InputStream(string))
                tokens = CommonTokenStream(lexer)
                parser = JavaParser(tokens)
                tree = parser.memberDeclaration()
                walker = ParseTreeWalker()
                listener = JavaParserListener()
                listener.variables = []
                listener.parameters = []
                listener.dataTypes = []
                listener.methodCalls = []
                walker.walk(listener, tree)
                methodInstance.variableList = listener.variables
                methodInstance.dataTypeList = listener.dataTypes
                methodInstance.funcCalleeList = listener.methodCalls
                methodInstance.parameterList = listener.parameters
            else:
                methodInstance.funcBody = " "
            methodInstance.funcId = funcId
            funcId+=1
            methodInstanceList.append(methodInstance)
            print(methodInstance.funcBody)
#            print(tree.toStringTree(recog=parser))
            #Not finished
    return methodInstanceList

#Shallow PYTHON code parser using Universal-Ctags
def parse_python_shallow(file):
    Command = "ctags -f - --kinds-python=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    methodList = astString.split('\n')
    member = re.compile(r'(member)')
    func = re.compile(r'(function)')
    number = re.compile(r'(\d+)')
    methodInstanceList = []

    for i in methodList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        methodInstance = function(file)
        methodInstance.funcBody = ''
        if i != '' and (member.match(elemList[3]) or func.match(elemList[3])):
            methodInstance.name = elemList[0]
            methodInstance.parentFile = elemList[1]
            methodInstance.lines = (int(number.search(elemList[4]).group(0)),
                                    int(number.search(elemList[5]).group(0)))
            methodInstance.parentNumLoc = len(lines)
            for line in range(methodInstance.lines[0], methodInstance.lines[1]):
                methodInstance.funcBody = methodInstance.funcBody + (lines[line])
            methodInstanceList.append(methodInstance)

    return methodInstanceList

#Deep PYTHON code parser using Universal-Ctags
def parse_python_deep(file):
    Command = "ctags -f - --kinds-python=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    methodList = astString.split('\n')
    member = re.compile(r'(member)')
    func = re.compile(r'(function)')
    number = re.compile(r'(\d+)')
    methodInstanceList = []

    for i in methodList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        methodInstance = function(file)
        methodInstance.funcBody = ''
        if i != '' and (member.match(elemList[3]) or func.match(elemList[3])):
            methodInstance.name = elemList[0]
            methodInstance.parentFile = elemList[1]
            methodInstance.lines = (int(number.search(elemList[4]).group(0)),
                                    int(number.search(elemList[5]).group(0)))
            methodInstance.parentNumLoc = len(lines)
            string = ""
            for line in range(methodInstance.lines[0], methodInstance.lines[1]):
                methodInstance.funcBody = methodInstance.funcBody + (lines[line])
            for line in range(methodInstance.lines[0]-1, methodInstance.lines[1]):
                string = string + (lines[line])
            string = textwrap.dedent(string)
            input = InputStream(string)
            lexer = Python3Lexer(input)
            tokens = CommonTokenStream(lexer)
            parser = Python3Parser(tokens)
            listener = Python3Listener()
            tree = parser.funcdef()
            listener.variables = []
            listener.parameters = []
            listener.funccalls = []
            walker = ParseTreeWalker()
            print(string)
            walker.walk(listener, tree)

            for i in listener.parameters:
                if re.findall("\w+", i):
                    methodInstance.parameterList.append(re.findall("\w+", i))

            for i in listener.variables:
                if re.search(r"^(.*?)(\=|\(|\-|\+|\[|\.|\,)", i).group(2) == '=' or re.search(r"^(.*?)(\=|\(|\-|\+|\[|\.|\,)", i).group(2) == ',':
                    methodInstance.variableList.append(re.search("^(.*?)(\=|\(|\-|\+|\[|\.|\,)", i).group(1))

            for i in listener.funccalls:
                print(i)
                if re.search(r"^(.*?)(\(|\=|\-|\+|\[|\,)", i):
                    if re.search(r"^(.*?)(\(|\=|\-|\+|\[|\,)", i).group(2) == '(':
                        methodInstance.funcCalleeList.append(re.search("^(.*?)(\(|\=|\-|\+|\[|\,)", i).group(1))
            print("Parameters: " + str(methodInstance.parameterList))
            print("Variables: " + str(methodInstance.variableList))
            print("Function calls: " + str(methodInstance.funcCalleeList))
            methodInstanceList.append(methodInstance)
            #Not finished
    return methodInstanceList

#Shallow GO code parser using Universal-Ctags
def parse_go_shallow(file):
    Command = "ctags -f - --kinds-go=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"
    functionInstanceList = []

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    functionList = astString.split('\n')
    func = re.compile(r'(func)')
    number = re.compile(r'(\d+)')
    funcBody = re.compile(r'{([\S\s]*)}')
    string = " "
    funcId = 1

    for i in functionList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        functionInstance = function(file)
        functionInstance.funcBody = ''
        if i != '' and func.fullmatch(elemList[3]) and len(elemList) >= 6:
            functionInstance.name = elemList[0]
            functionInstance.parentFile = elemList[1]
            functionInstance.parentNumLoc = len(lines)
            functionInstance.lines = (int(number.search(elemList[4]).group(0)),
                                    int(number.search(elemList[5]).group(0)))
            string = " "
            string = string.join(lines[functionInstance.lines[0]:functionInstance.lines[1]])
            if funcBody.search(string):
                functionInstance.funcBody = functionInstance.funcBody + funcBody.search(string).group(1)
            else:
                functionInstance.funcBody = " "
            functionInstance.funcId = funcId
            funcId += 1
            functionInstanceList.append(functionInstance)

    return functionInstanceList

#Deep GO code parser using Universal-Ctags
def parse_go_deep(file):
    Command = "ctags -f - --kinds-go=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"
    functionInstanceList = []

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    functionList = astString.split('\n')
    func = re.compile(r'(func)')
    number = re.compile(r'(\d+)')
    funcBody = re.compile(r'{([\S\s]*)}')
    string = " "
    funcId = 1

    for i in functionList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        functionInstance = function(file)
        functionInstance.funcBody = ''
        if i != '' and func.fullmatch(elemList[3]) and len(elemList) >= 6:
            functionInstance.name = elemList[0]
            functionInstance.parentFile = elemList[1]
            functionInstance.parentNumLoc = len(lines)
            functionInstance.lines = (int(number.search(elemList[4]).group(0)),
                                    int(number.search(elemList[5]).group(0)))
            string = " "
            string = string.join(lines[functionInstance.lines[0]-1:functionInstance.lines[1]])
            if funcBody.search(string):
                functionInstance.funcBody = functionInstance.funcBody + funcBody.search(string).group(1)
            else:
                functionInstance.funcBody = " "
            functionInstance.funcId = func
            funcId += 1
            stream = InputStream(string)
            lexer = GoLexer(stream)
            tokens = CommonTokenStream(lexer)
            parser = GoParser(tokens)
            tree = parser.sourceFile()
            listener = GoParserListener()
            walker = ParseTreeWalker()
            listener.dataTypes = []
            listener.parameters = []
            listener.variables = []
            listener.funcCalls = []
            listener.expressions = []
            walker.walk(listener, tree)
            parameters = []

            functionInstance.dataTypeList = listener.dataTypes
            for i in listener.parameters:
                match = re.findall(r"(?:(?<=\b)\w+|\b(?!)\w+)(?=[, ]|$)", i)
                if match:
                    for j in match:
                        functionInstance.parameterList.append(j)
            for i in listener.variables:
                variable = re.findall("\w+", i)
                for j in functionInstance.dataTypeList:
                    if re.search("(" + str(j) + ").*$", i):
                        variable = re.sub("(" + str(j) + ").*$", "", i)
                        functionInstance.variableList.append(variable)
                        continue
                functionInstance.variableList.extend(variable)
            for i in listener.funcCalls:
                for j in listener.expressions:
                    if re.search("(" + str(i) + "\()", j):
                        functionInstance.funcCalleeList.append(i)
            print(string)
            print("Parameters: " + str(functionInstance.parameterList))
            print("Variables: " + str(functionInstance.variableList))
            print("Data types: " + str(functionInstance.dataTypeList))
            print("Func calls: " + str(functionInstance.funcCalleeList))
            functionInstanceList.append(functionInstance)

    return functionInstanceList

#Shallow JavaScript code parser using Universal-Ctags
def parse_js_shallow(file):
    Command = "ctags -f - --kinds-javascript=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"
    functionInstanceList = []

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    functionList = astString.split('\n')
    func = re.compile(r'(function)')
    method = re.compile(r'(method)')
    number = re.compile(r'(\d+)')
    new_line = re.compile(r'(\n)')
    funcB = pcre.compile(r'function[^{]+({(?:[^{}]+|(?-1))*+})')

    string = " "
    funcId = 1
    lines_count = 0

    for i in functionList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        functionInstance = function(file)
        functionInstance.funcBody = ''
        if i != '' and len(elemList) >= 5 and (func.fullmatch(elemList[3]) or method.fullmatch(elemList[3])):
            functionInstance.name = elemList[0]
            functionInstance.parentFile = elemList[1]
            functionInstance.parentNumLoc = len(lines)
            string = " "
            string = string.join(lines[int(number.search(elemList[4]).group(0))-1:])
            if funcB.search(string):
                functionInstance.funcBody = functionInstance.funcBody + funcB.search(string).group(1)[1:-1]
            else:
                functionInstance.funcBody = " "
            functionInstance.lines = (int(number.search(elemList[4]).group(0)),
                                      int(number.search(elemList[4]).group(0)) + functionInstance.funcBody.count("\n"))
            functionInstance.funcId = funcId
            funcId += 1
            functionInstanceList.append(functionInstance)

    return functionInstanceList

#Shallow JavaScript code parser using Universal-Ctags
def parse_js_deep(file):
    Command = "ctags -f - --kinds-javascript=* --fields=neK " + file
    global delimiter
    delimiter = "\r\0?\r?\0\r"
    functionInstanceList = []

    try:
        astString = subprocess.check_output(Command, stderr=subprocess.STDOUT, shell=True).decode()

    except subprocess.CalledProcessError as e:
        print("Parser Error:", e)
        astString = ""

    f = open(file, 'r')
    lines = f.readlines()
    functionList = astString.split('\n')
    func = re.compile(r'(function)')
    method = re.compile(r'(method)')
    number = re.compile(r'(\d+)')
    new_line = re.compile(r'(\n)')
    funcB = pcre.compile(r'function[^{]+({(?:[^{}]+|(?-1))*+})')

    string = " "
    funcId = 1
    lines_count = 0

    for i in functionList:
        elemList = re.sub(r'[\t\s ]{2,}', '', i)
        elemList = elemList.split("\t")
        functionInstance = function(file)
        functionInstance.funcBody = ''
        if i != '' and len(elemList) >= 5 and (func.fullmatch(elemList[3]) or method.fullmatch(elemList[3])):
            functionInstance.name = elemList[0]
            functionInstance.parentFile = elemList[1]
            functionInstance.parentNumLoc = len(lines)
            string = " "
            string = string.join(lines[int(number.search(elemList[4]).group(0))-1:])
            if funcB.search(string):
                functionInstance.funcBody = functionInstance.funcBody + funcB.search(string).group(1)[1:-1]
            else:
                functionInstance.funcBody = " "
            functionInstance.lines = (int(number.search(elemList[4]).group(0)),
                                      int(number.search(elemList[4]).group(0)) + functionInstance.funcBody.count("\n"))
            functionInstance.funcId = funcId
            funcId += 1
#For function parameters
            text = ""
            text = text.join(lines[functionInstance.lines[0]-1:functionInstance.lines[1]])
            input = InputStream(text)
            lexer = JavaScriptLexer(input)
            tokens = CommonTokenStream(lexer)
            parser = JavaScriptParser(tokens)
            tree = parser.functionBody()
            listener = JavaScriptParserListener()
            listener.variables = []
            listener.identifiers = []
            listener.parameters = []
            walker = ParseTreeWalker()
            walker.walk(listener, tree)

            for i in listener.identifiers:
                funccall = re.compile("" + str(i) + "\(")
                if funccall.search(text):
                    functionInstance.funcCalleeList.append(i)
            functionInstance.parameterList = listener.parameters
            functionInstance.variableList = listener.variables
            functionInstanceList.append(functionInstance)

    return functionInstanceList



def loadSource(rootDirectory):
    # returns the list of .src files under the specified root directory.
    maxFileSizeInBytes = None
    maxFileSizeInBytes = 2 * 1024 * 1024  # remove this line if you don't want to restrict
    # the maximum file size that you process.
    walkList = os.walk(rootDirectory)
    srcFileList = []
    for path, dirs, files in walkList:
        for fileName in files:
            ext = fileName.lower()
            if ext.endswith('.c') or ext.endswith('.cpp') or ext.endswith('.cc') or ext.endswith('.c++') or ext.endswith('.cxx') or ext.endswith('.java') or ext.endswith('.py') or ext.endswith('.go') or ext.endswith('.js'):
                absPathWithFileName = path.replace('\\', '/') + '/' + fileName
                if os.path.getsize(absPathWithFileName) < maxFileSizeInBytes:
                    if maxFileSizeInBytes is not None:
                        srcFileList.append(absPathWithFileName)
                    else:
                        srcFileList.append(absPathWithFileName)
    return srcFileList

#old
def parseFile_deep_multi(f):
    functionInstanceList = parse_deep(f)
    return (f, functionInstanceList)
def parseFile_shallow_multi(f):
    functionInstanceList = parse_shallow(f)
    return (f, functionInstanceList)


#new
def parseFile_java_shallow(f):
    methodInstanceList = parse_java_shallow(f)
    return (f, methodInstanceList)

def parseFile_python_shallow(f):
    methodInstanceList = parse_python_shallow(f)
    return (f, methodInstanceList)

def parseFile_go_shallow(f):
    functionInstanceList = parse_go_shallow(f)
    return (f, functionInstanceList)

def parseFile_js_shallow(f):
    functionInstanceList = parse_js_shallow(f)
    return (f, functionInstanceList)


#parse_python_deep("hmark.py")
#parse_go_deep("testcode1/system.go")
#parse_js_deep("testcode1/nginx-conf-master/src/conf.js")
parse_go_deep("testcode1/system.go")

#start = time.time()
#parse_c_deep("testcode/trace.c")
#for i in parse_c_deep("testcode/async.c"):
#    orig, abst = new_abstract(i, 4)
#    print(abst)
#end = time.time()
#print(end - start)
#start = time.time()
#end = time.time()
#print(end - start)
#parse_java_deep("testcode/sample_java/javatest/sample1.java")
#parse_python_deep("hmark.py")
#parse_java_deep("testcode/spring-framework-master")
#fileList = loadSource("testcode/react-master")
#directory = "testcode/react-master"
#cpu_count = get_cpu_count.get_cpu_count()
#if cpu_count != 1:
#    cpu_count -= 1
#fileList = loadSource("testcode1")
#directory = "testcode1"
#numFunc = 0
#projDic = {}
#hashFileMap = {}
#proj = directory.replace('\\', '/').split('/')[-1]

#pool = multiprocessing.Pool(processes=cpu_count)

#start = time.time()
#count = 0
#for idx, tup in enumerate(pool.imap_unordered(parse_js_deep, fileList)):
#    print(idx)
#    count+=1
#    f = tup[0]
#    methodInstanceList = tup[1]
##    numFunc += len(methodInstanceList)
#end = time.time()
#print(end - start)
#    for f in methodInstanceList:
##        origBody, absBody = abstract(f, 0)

#        absBody = normalize(absBody)
#        funcLen = len(absBody)
#        if funcLen > 50:
#            hashValue = md5(absBody.encode('utf-8')).hexdigest()
#
#            try:
#                projDic[funcLen].append(hashValue)
#            except KeyError:
#                projDic[funcLen] = [hashValue]
#            try:
#                hashFileMap[hashValue].extend([pathOnly, f.funcId])
#            except KeyError:
#                hashFileMap[hashValue] = [pathOnly, f.funcId]
#        else:
#            numFunc -= 1  # decrement numFunc by 1 if funclen is under threshold


################################################################################
#cpu_count = get_cpu_count.get_cpu_count()
#if cpu_count != 1:
#    cpu_count -= 1
#
#fileList = loadSource("testcode1")
#directory = "testcode1"
#numFunc = 0
#absLevel = 4
#projDic = {}
#hashFileMap = {}
#proj = directory.replace('\\', '/').split('/')[-1]
#
#pool = multiprocessing.Pool(processes=cpu_count)
#for idx, tup in enumerate(pool.imap_unordered(parseFile_deep_multi, fileList)):
#    f = tup[0]
#
#    functionInstanceList = tup[1]
#    pathOnly = f.split(proj, 1)[1][1:]
#    numFunc += len(functionInstanceList)
#    for f in functionInstanceList:
#        f.removeListDup()
#        path = f.parentFile
#        origBody, absBody = abstract(f, absLevel)
#        print(origBody)
#        print("**********************************")
#        print(absBody)
#        print("**********************************")
#        absBody = normalize(absBody)
#        print(absBody)
#        funcLen = len(absBody)
#
#        if funcLen > 50:
#            hashValue = md5(absBody.encode('utf-8')).hexdigest()
#            print(hashValue)
#
#            try:
#                projDic[funcLen].append(hashValue)
#            except KeyError:
#                projDic[funcLen] = [hashValue]
#            try:
#                hashFileMap[hashValue].extend([pathOnly, f.funcId])
#            except KeyError:
#                hashFileMap[hashValue] = [pathOnly, f.funcId]
#        else:
#            numFunc -= 1  # decrement numFunc by 1 if funclen is under threshold
