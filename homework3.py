import sys
import inspect
from collections import defaultdict


class KnowledgeBase:
    # Rules stores all rules as strings
    rules = []

    # Stores rules with a id
    ruleStore = defaultdict(list)

    ruleCount = 0

    def __init__(self, rules):
        self.rules = rules
        self.ruleCount = 0
        for i in range(len(rules)):
            self.rules[i] = self.convertCNF(self.rules[i])

    def convertCNF(self, rule):
        tokens = rule.split(' ')

        if len(tokens) > 2 and "=>" in tokens:
            return self.convertImplicationToCNF(tokens)
        else:
            return rule

    def isNegative(self, query):
        return query[0] == '~'

    def convertImplicationToCNF(self, tokens):
        cnfRule = []
        implicationReached = False
        for i in tokens:
            if not implicationReached and (i != "=>" and i != "&"):
                if self.isNegative(i):
                    cnfRule.append(i[1:])
                else:
                    cnfRule.append('~' + i)
            elif i == "=>":
                cnfRule.append("|")
                implicationReached = True
            elif i == "&":
                cnfRule.append("|")
            else:
                cnfRule.append(i)

        return " ".join(cnfRule)


class ReaderWriter:

    def __init__(self, inputFile, outputFile):
        self.queries = []
        self.kb = []
        self.inputFile = inputFile
        self.outputFile = outputFile
        self.sentences = []
        self.cnfConvertor = None
        self.readFileObject = None
        self.writeFileObject = None
        self.prologue()

    def prologue(self):
        self.writeFileObject = open(self.outputFile, 'w')
        try:
            self.readFileObject = open(self.inputFile, 'r')
        except IOError:
            self.writeFileObject.write("File not found: {}".format(self.inputFile))
            self.writeFileObject.close()
            sys.exit()

    def epilogue(self):
        self.readFileObject.close()
        self.writeFileObject.close()

    def read(self):
        lines = self.readFileObject.readlines()
        for index, line in enumerate(lines):
            if index == 0:
                numQueries = int(lines[index].strip())
                for i in range(1, numQueries + 1):
                    self.queries.append(lines[i].strip())
                numSentences = int(lines[numQueries + 1].strip())
                for i in range(numQueries + 2, numQueries + numSentences + 2):
                    self.kb.append(lines[i].strip())
                break

        # Convert to CNF
        self.cnfConvertor = KnowledgeBase(self.kb)
        self.sentences = self.cnfConvertor.rules
        return self.queries, self.sentences

    def write(self, flag):
        if flag:
            self.writeFileObject.write("TRUE\n")
        else:
            self.writeFileObject.write("FALSE\n")

    def isNegative(self, query):
        return query[0] == '~'


class Solver:

    def __init__(self, readerWriter, sentences, queries):
        self.readerWriter = readerWriter
        self.singleTermSentences = []
        self.sentences = sentences
        self.queries = queries
        self.positiveKB = defaultdict(list)
        self.negatedKB = defaultdict(list)

        for i in sentences:
            if self.ifVariableExists(i):
                self.singleTermSentences.append(i)

    def splitKB(self):
        for item in self.sentences:
            data = item.split(' | ')
            for i in [i.replace(' ', '') for i in data]:
                if self.isNegative(i):
                    b = i[1:].split("(")[0]
                    self.negatedKB[b].append(item)
                else:
                    b = i.split("(")[0]
                    self.positiveKB[b].append(item)

    def solve(self):
        self.splitKB()

        for query in self.queries:
            if self.isNegative(query):
                newQuery = query[1:]
            else:
                newQuery = "~" + query
            self.readerWriter.write(self.unification(newQuery, newQuery))

    @staticmethod
    def isNegative(query):
        return query[0] == '~'

    @staticmethod
    def isVariable(var):
        return var[0].islower()

    @staticmethod
    def getPredicateConstant(term):
        splitQuery = term.split('(')
        return splitQuery[0], splitQuery[1][:-1]

    @staticmethod
    def collapseORs(sentence):
        if " |  | " in sentence:
            sentence = sentence.replace(" |  | ", " | ")
        if sentence[:3] == " | ":
            sentence = sentence[3:]
        if sentence[-3:] == " | ":
            sentence = sentence[:-3]

        return sentence

    @staticmethod
    def replaceVariableWithConstant(word, replaceString, replaceVar):
        temp = replaceString.replace("(" + word + ")", "(" + replaceVar + ")")
        temp = temp.replace("(" + word + ",", "(" + replaceVar + ",")
        temp = temp.replace("," + word + ")", "," + replaceVar + ")")
        return temp.replace("," + word + ",", "," + replaceVar + ",")

    # Checks if a variable exists
    def ifVariableExists(self, sentence):
        if " | " in sentence:
            return False

        constants = sentence.split('(')[1][:-1]
        constantsList = constants.split(",")

        for val in constantsList:
            if self.isVariable(val):
                return False
        return True

    def getRemoveQueries(self, query, tempQuery, sentence):
        if not self.isNegative(query):
            return sentence[1:], "~" + tempQuery
        else:
            return "~" + sentence, tempQuery[1:]

    def unification(self, query, remainderQuery):

        # Stack Overflow Checker
        if len(inspect.stack(0)) > 600:
            return False

        predicate = query.split('(')[0]

        try:
            if self.isNegative(query):
                value = self.positiveKB[predicate[1:]]
            else:
                value = self.negatedKB[predicate]
        except KeyError:
            return False

        for sentence in value:
            remainderQueryCopy = remainderQuery
            queryCopy = query

            rQuery1, rQuery2 = self.getRemoveQueries(query, query, sentence)
            if sentence in self.singleTermSentences:
                flag1, resolvedQuery1 = self.resolutionStep(remainderQueryCopy, rQuery1)
                flag2 = True
                resolvedQuery2 = ""
            else:
                flag1, resolvedQuery1 = self.resolutionStep(remainderQueryCopy, queryCopy)
                flag2, resolvedQuery2 = self.resolutionStep(sentence, rQuery2)
            if not flag1 or not flag2:
                continue
            else:
                if not resolvedQuery1 and not resolvedQuery2:
                    remainderQueryCopy = ''
                elif not resolvedQuery2 and resolvedQuery1:
                    remainderQueryCopy = resolvedQuery1
                elif not resolvedQuery1 and resolvedQuery2:
                    remainderQueryCopy = resolvedQuery2
                else:
                    remainderQueryCopy = resolvedQuery2 + " | " + resolvedQuery1

                if not remainderQueryCopy:
                    return True
                else:
                    data = remainderQueryCopy.split(" | ")
                    for i in data:
                        if self.unification(i, remainderQueryCopy):
                            return True
                        else:
                            break

        return False

    def resolutionStep(self, sentence, query):
        queryPredicate, queryArgs = self.getPredicateConstant(query)
        queryArgsList = queryArgs.split(",")

        sentenceTerms = sentence.split(" | ")
        flag = False

        for term in sentenceTerms:
            count = 0
            sentencePredicate, sentenceArgs = self.getPredicateConstant(term)

            if sentencePredicate == queryPredicate:
                sentenceArgsList = sentenceArgs.split(",")

                for j in sentenceArgsList:
                    if not self.isVariable(j) and self.isVariable(queryArgsList[count]):
                        query = self.replaceVariableWithConstant(queryArgsList[count], query, j)
                        flag = True
                        count += int(flag)
                    elif self.isVariable(j) and not self.isVariable(queryArgsList[count]):
                        sentence = self.replaceVariableWithConstant(j, sentence, queryArgsList[count])
                        flag = True
                        count += int(flag)
                    elif self.isVariable(j) and self.isVariable(queryArgsList[count]):
                        flag = True
                        if not (j == queryArgsList[count]):
                            sentence = self.replaceVariableWithConstant(j, sentence, queryArgsList[count])
                        count += int(flag)
                    elif not self.isVariable(j) and not self.isVariable(queryArgsList[count]):
                        flag = (j == queryArgsList[count])
                        if flag:
                            count += int(flag)
                        else:
                            break

                if flag:
                    sentence = self.collapseORs(sentence.replace(query, ""))
                    return flag, sentence

        return flag, sentence


if __name__ == '__main__':
    r = ReaderWriter("input.txt", "output.txt")
    r.read()
    solver = Solver(r, sentences=r.sentences, queries=r.queries)
    solver.solve()
    r.epilogue()
