import sys
import re
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

    def convert_implication_to_cnf(self, tokens):
        cnfRule = []
        implicationReached = False
        for i in tokens:
            if not implicationReached and (i != "=>" and i != "&"):
                cnfRule.append("~" + i)
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
        self.nq = None
        self.ns = None
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
                self.nq = int(lines[index].strip("\n"))
                for i in range(1, self.nq + 1):
                    self.queries.append(lines[i].strip("\n"))
                self.ns = int(lines[self.nq + 1].strip("\n"))
                for i in range(self.nq + 2, self.nq + self.ns + 2):
                    self.kb.append(lines[i].strip("\n"))
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

    def splitKB(self):
        negatedKB = defaultdict(list)
        positiveKB = defaultdict(list)

        for item in self.sentences:
            data = item.split('|')
            for i in [i.replace(' ', '') for i in data]:
                if isNegative(i):
                    b = i[1:].split("(")[0]
                    negatedKB[b].append(item)
                else:
                    b = i.split("(")[0]
                    positiveKB[b].append(item)

        return negatedKB, positiveKB


def extract_constants(query):
    variable = re.search(r'\((.*?)\)', query).group(1)
    return variable


def isVariable(var):
    return var[0].islower()


# Checks if a variable exists
def checkSentence(sentence):
    if " | " in sentence:
        return False

    constants = sentence.split('(')[1][:-1]
    constantsList = constants.split(",")

    for val in constantsList:
        if not isVariable(val):
            return False
    return True


def isNegative(query):
    return query[0] == '~'


def getRemoveQueries(query, query_temp, sentence):
    if not isNegative(query):
        return sentence[1:], "~" + query_temp
    else:
        return "~" + sentence, query_temp[1:]


def unification(query, left_over, positiveKB, negativeKB, can_simplyfy):
    predicate = query.split('(')[0]

    value = None

    if not isNegative(query):
        try:
            value = negativeKB[predicate]
        except KeyError:
            return False
    else:
        try:
            value = positiveKB[predicate[1:]]
        except KeyError:
            return False

    for sentence in value:
        try:
            left_over_temp = left_over
            query_temp = query

            rQuery1, rQuery2 = getRemoveQueries(query, query_temp, sentence)

            if sentence in can_simplyfy:
                ret1, l1 = remove(left_over_temp, rQuery1)
                ret2 = 1
                l2 = ""
            else:
                ret1, l1 = remove(left_over_temp, query_temp)
                ret2, l2 = remove(sentence, rQuery2)
            if ret1 == 0 or ret2 == 0:
                continue
            else:
                if l1 == '' and l2 != '':
                    left_over_temp = l2
                elif l2 == '' and l1 != '':
                    left_over_temp = l1
                elif l1 == '' and l2 == '':
                    left_over_temp = ''
                else:
                    left_over_temp = l2 + " | " + l1

                if left_over_temp == '':
                    return True
                else:
                    if "|" in left_over_temp:
                        data = left_over_temp.split("|")
                        for i in data:
                            i = i.replace(" ", "")
                            if unification(i, left_over_temp, positiveKB, negativeKB, can_simplyfy):
                                return True
                            else:
                                break
                    else:
                        if unification(left_over_temp, left_over_temp, positiveKB, negativeKB, can_simplyfy):
                            return True
                        else:
                            continue
        except RuntimeError as re:
            if re.args[0] == 'maximum recursion depth exceeded':
                return False

    return False


def collapseORs(sentence):
    if " |  | " in sentence:
        news2 = sentence.replace(" |  | ", " | ")
        return news2
    elif sentence[:3] == " | ":
        news2 = sentence[3:]
        return news2
    elif sentence[-3:] == " | ":
        news2 = sentence[:-3]
        return news2
    else:
        return sentence


def remove(k, query):
    substitutionPass, updatedQuery, updatedSentence = querySubstitution(k, query)

    if substitutionPass:
        if updatedQuery in updatedSentence:
            news1 = updatedSentence.replace(updatedQuery, "")
        else:
            sentencePrefix = updatedSentence.find(query.partition("(")[0])
            sentenceSuffix = updatedSentence.find(')', sentencePrefix)
            deletionString = updatedSentence[sentencePrefix:sentenceSuffix + 1]
            news1 = updatedSentence.replace(deletionString, "")

        # Collapse OR's
        return 1, collapseORs(news1)
    else:
        return 0, updatedSentence


def getPredicateConstant(term):
    split_query = term.split('(')
    return split_query[0], split_query[1][:-1]


def querySubstitution(sentence, query):
    queryPredicate, queryArgs = getPredicateConstant(query)
    queryArgsList = queryArgs.split(",")

    sentenceTerms = sentence.split(" | ")
    flag = False
    for term in sentenceTerms:

        count = 0
        sentencePredicate, sentenceArgs = getPredicateConstant(term)

        if sentencePredicate == queryPredicate:
            sentenceArgsList = sentenceArgs.split(",")

            for j in sentenceArgsList:
                if not isVariable(j) and isVariable(queryArgsList[count]):
                    query = replaceVariableWithConstant(queryArgsList[count], query, j)
                    flag = True
                    count += 1
                elif isVariable(j) and not isVariable(queryArgsList[count]):
                    sentence = replaceVariableWithConstant(j, sentence, queryArgsList[count])
                    flag = True
                    count += 1
                elif not isVariable(j) and not isVariable(queryArgsList[count]):
                    flag = (j == queryArgsList[count])
                    if flag:
                        count += 1
                    else:
                        break
                elif isVariable(j) and isVariable(queryArgsList[count]):
                    if not (j == queryArgsList[count]):
                        sentence = replaceVariableWithConstant(j, sentence, queryArgsList[count])
                        flag = True
                    else:
                        flag = True
                    count += 1
            if flag:
                break

    return flag, query, sentence


def replaceVariableWithConstant(word, to_replace, with_replace):
    big_regex = re.compile(r'\b%s\b' % r'\b|\b'.join(map(re.escape, word)))
    a = big_regex.sub(with_replace, to_replace)
    return (a)


def main():
    r = ReaderWriter("input.txt", "output.txt")
    query_list, sentences = r.read()
    negativeKB, positiveKB = r.splitKB()

    can_simplyfy = []
    for a in sentences:
        if checkSentence(a):
            can_simplyfy.append(a)

    for query in query_list:
        new_query = None
        if isNegative(query):
            new_query = query[1:]
        else:
            new_query = "~" + query
        r.write(unification(new_query, new_query, positiveKB, negativeKB, can_simplyfy))

    r.epilogue()


if __name__ == '__main__':
    main()
