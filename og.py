from collections import defaultdict
import copy


class Literal:
    predicate = None
    argCount = 0
    args = []
    isVariable = []
    negated = False
    basePredicate = None

    def __init__(self, token):
        # Token is of the format Predicate(Args....)
        subTokens = token.split('(')
        self.predicate = subTokens[0]
        self.basePredicate = self.predicate
        self.args = subTokens[1][:-1].split(',')
        self.argCount = len(self.args)
        self.isVariable = [False for i in range(self.argCount)]
        self.negated = ("~" == self.predicate[0])

        if self.negated:
            self.basePredicate = self.basePredicate[1:]

        for idx, i in enumerate(self.args):
            if self.args[idx][0].islower():
                self.isVariable[idx] = True

    def __str__(self):
        return self.predicate + "(" + ",".join(self.args) + ")"


class KnowledgeBase:
    # Rules stores all rules as strings
    rules = []

    # Stores rules with a id
    ruleStore = defaultdict(list)
    ruleExistence = defaultdict(bool)

    ruleCount = 0

    def __init__(self, rules):
        self.rules = rules
        self.ruleCount = 0
        for i in range(len(rules)):
            self.rules[i] = self.convert_to_CNF(self.rules[i])
        self.generateRuleStore()

    def convert_to_CNF(self, rule):
        tokens = rule.split(' ')

        if len(tokens) > 2:
            return self.convert_implication_to_cnf(tokens)
        else:
            return rule

    def convert_implication_to_cnf(self, tokens):
        # p => q becomes ~p or q
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

    def generateRuleStore(self):
        for i in self.rules:
            tokens = i.strip().split(' ')
            tempRule = []
            ruleString = ""
            for j in tokens:
                if j != '|':
                    tempRule.append(Literal(j))
            self.ruleStore[self.ruleCount] = tempRule
            self.ruleCount += 1
            self.ruleExistence[i] = True

    def printRules(self):
        for i in self.ruleExistence:
            if self.ruleExistence[i]:
                print(i)

    def unifyLiterals(self, first: Literal, second: Literal):
        # Check if they can be unified, then return as assignment dict
        firstU = copy.deepcopy(first)
        secondU = copy.deepcopy(second)
        assignment = {}

        for idx in range(first.argCount):
            if first.isVariable[idx] and not second.isVariable[idx]:
                assignment[first.args[idx]] = second.args[idx]
                firstU.args[idx] = second.args[idx]
                firstU.isVariable[idx] = False
            elif not first.isVariable[idx] and second.isVariable[idx]:
                assignment[second.args[idx]] = first.args[idx]
                secondU.args[idx] = first.args[idx]
                secondU.isVariable[idx] = False
            elif not first.isVariable[idx] and not second.isVariable[idx]:
                if first.args[idx] != second.args[idx]:
                    return firstU, secondU, assignment
            else:
                # Assumes variables have been normalized
                assignment[secondU.args[idx]] = first.args[idx]
                secondU.args[idx] = first.args[idx]

        print("--- Rule Unification ----")
        print("Unified First:  ", first)
        print("Unified Second: ", second)
        print("Assignment:     ", assignment)
        return firstU, secondU, assignment

    def unifyRules(self, rule1, rule2):
        f = None
        s = None
        assignment = {}
        flag = False

        for i, first in enumerate(self.ruleStore[rule1]):
            for j, second in enumerate(self.ruleStore[rule2]):
                if first.negated and not second.negated:
                    if first.basePredicate == second.basePredicate:
                        f, s, assignment = self.unifyLiterals(first, second)
                        flag = True
                elif not first.negated and second.negated:
                    if first.basePredicate == second.basePredicate:
                        f, s, assignment = self.unifyLiterals(first, second)
                        flag = True
                if flag:
                    break
            if flag:
                break

        resolutionRule = []
        if flag:
            candidateOne = copy.deepcopy(self.ruleStore[rule1])
            candidateTwo = copy.deepcopy(self.ruleStore[rule2])

            for i in candidateOne:
                for cnt in range(i.argCount):
                    try:
                        i.args[cnt] = assignment[i.args[cnt]]
                    except KeyError:
                        pass
            for i in candidateTwo:
                for cnt in range(i.argCount):
                    try:
                        i.args[cnt] = assignment[i.args[cnt]]
                    except KeyError:
                        pass

            for i in candidateOne:
                if str(i) != str(f):
                    resolutionRule.append(i)
            for i in candidateTwo:
                if str(i) != str(s):
                    resolutionRule.append(i)

        # Returns a flag and a rule which could possibly be blank
        return flag, resolutionRule

    def unifyKB(self):
        # TODO: Use assignment from UnifyLiterals to convert vars to those constants in every other literal

        flag = False

        for i in range(self.ruleCount):
            for j in range(i + 1, self.ruleCount):
                temp, newRule = self.unifyRules(i, j)
                newRuleString = " | ".join(map(str, newRule))
                if temp and newRuleString != "" and not self.ruleExistence[newRuleString]:
                    flag = True
                    self.ruleStore[self.ruleCount] = newRule
                    self.ruleCount += 1
                    self.ruleExistence[newRuleString] = True
            if flag:
                break


# Input
n = int(input().strip())
queries = []
for i in range(0, n):
    queries.append(input().strip())
k = int(input().strip())
KB = []
for i in range(0, k):
    KB.append(input().strip())

kb = KnowledgeBase(KB)
#
# for i in kb.ruleStore:
#     for j in kb.ruleStore[i]:
#         print(str(j))

kb.printRules()
print(kb.rules)
kb.unifyKB()
print()
kb.printRules()
