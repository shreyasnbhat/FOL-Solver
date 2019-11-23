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
            self.rules[i] = self.convert_to_CNF(self.rules[i])

    def convert_to_CNF(self, rule):
        tokens = rule.split(' ')

        if len(tokens) > 2 and "=>" in tokens:
            return self.convert_implication_to_cnf(tokens)
        else:
            return rule

    def isNegative(self, query):
        return query[0] == '~'

    def convert_implication_to_cnf(self, tokens):
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
                nq = int(lines[index].strip())
                for i in range(1, nq + 1):
                    self.queries.append(lines[i].strip())
                ns = int(lines[nq + 1].strip())
                for i in range(nq + 2, nq + ns + 2):
                    self.kb.append(lines[i].strip())
                break

        # Convert to CNF
        self.cnfConvertor = KnowledgeBase(self.kb)
        self.sentences = self.cnfConvertor.rules
        return self.queries, self.sentences

    def write(self, flag):
        if flag:
            self.writeFileObject.write("TRUE" + "\n")
        else:
            self.writeFileObject.write("FALSE" + "\n")

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
            if self.checkSentence(i):
                self.singleTermSentences.append(i)

    def splitKB(self):
        for item in self.sentences:
            data = item.split('|')
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
        split_query = term.split('(')
        return split_query[0], split_query[1][:-1]

    @staticmethod
    def collapseORs(sentence):
        if " |  | " in sentence:
            newSentence = sentence.replace(" |  | ", " | ")
        elif sentence[:3] == " | ":
            newSentence = sentence[3:]
        elif sentence[-3:] == " | ":
            newSentence = sentence[:-3]
        else:
            newSentence = sentence

        return newSentence

    @staticmethod
    def replaceVariableWithConstant(word, to_replace, with_replace):
        temp = to_replace.replace("(" + word + ")", "(" + with_replace + ")")
        temp = temp.replace("(" + word + ",", "(" + with_replace + ",")
        temp = temp.replace("," + word + ")", "," + with_replace + ")")
        return temp.replace("," + word + ",", "," + with_replace + ",")

    # Checks if a variable exists
    def checkSentence(self, sentence):
        if " | " in sentence:
            return False

        constants = sentence.split('(')[1][:-1]
        constantsList = constants.split(",")

        for val in constantsList:
            if self.isVariable(val):
                return False
        return True

    def getRemoveQueries(self, query, query_temp, sentence):
        if not self.isNegative(query):
            return sentence[1:], "~" + query_temp
        else:
            return "~" + sentence, query_temp[1:]

    def unification(self, query, left_over):

        # Stack Overflow Checker
        if len(inspect.stack(0)) > 400:
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
            try:
                remainderQuery = left_over
                queryCopy = query

                rQuery1, rQuery2 = self.getRemoveQueries(query, queryCopy, sentence)
                if sentence in self.singleTermSentences:
                    flag1, l1 = self.removeTerm(remainderQuery, rQuery1)
                    flag2 = True
                    l2 = ""
                else:
                    flag1, l1 = self.removeTerm(remainderQuery, queryCopy)
                    flag2, l2 = self.removeTerm(sentence, rQuery2)
                if not flag1 or not flag2:
                    continue
                else:
                    if not l1 and not l2:
                        remainderQuery = ''
                    elif not l2 and l1:
                        remainderQuery = l1
                    elif not l1 and l2:
                        remainderQuery = l2
                    else:
                        remainderQuery = l2 + " | " + l1

                    if not remainderQuery:
                        return True
                    else:
                        data = remainderQuery.split(" | ")
                        for i in data:
                            if self.unification(i, remainderQuery):
                                return True
                            else:
                                break
            except RuntimeError as re:
                print("Depth Limit")
                if re.args[0] == 'maximum recursion depth exceeded':
                    return False

        return False

    def removeTerm(self, k, query):
        substitutionPass, updatedQuery, updatedSentence = self.querySubstitution(k, query)

        if substitutionPass:
            if updatedQuery in updatedSentence:
                newSentence = updatedSentence.replace(updatedQuery, "")
            else:
                sentencePrefix = updatedSentence.find(query.split("(")[0])
                sentenceSuffix = updatedSentence.find(')', sentencePrefix)
                deletionString = updatedSentence[sentencePrefix:sentenceSuffix + 1]
                newSentence = updatedSentence.replace(deletionString, "")

            # Collapse OR's
            return True, self.collapseORs(newSentence)
        else:
            return False, updatedSentence

    def querySubstitution(self, sentence, query):

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
                        count += 1
                    elif self.isVariable(j) and not self.isVariable(queryArgsList[count]):
                        sentence = self.replaceVariableWithConstant(j, sentence, queryArgsList[count])
                        flag = True
                        count += 1
                    elif not self.isVariable(j) and not self.isVariable(queryArgsList[count]):
                        flag = (j == queryArgsList[count])
                        if flag:
                            count += 1
                        else:
                            break
                    elif self.isVariable(j) and self.isVariable(queryArgsList[count]):
                        if not (j == queryArgsList[count]):
                            sentence = self.replaceVariableWithConstant(j, sentence, queryArgsList[count])
                            flag = True
                        else:
                            flag = True
                        count += 1
                if flag:
                    break

        return flag, query, sentence


if __name__ == '__main__':
    r = ReaderWriter("input3.txt", "output.txt")
    r.read()
    solver = Solver(r, sentences=r.sentences, queries=r.queries)
    solver.solve()
    r.epilogue()
