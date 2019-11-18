import sys
import re

queries = list()
kb = list()
nq = 0
ns = 0


def get_input():
    fin = "input.txt"
    output_file = "output.txt"
    global queries
    global kb
    global nq
    global ns

    try:
        input_file = open(fin, 'r')
        lines = input_file.readlines()
        for index, line in enumerate(lines):
            if index == 0:
                nq = int(lines[index].strip("\n"))
                for i in range(1, nq + 1):
                    queries.append(lines[i].strip("\n"))
                ns = int(lines[nq + 1].strip("\n"))
                for i in range(nq + 2, nq + ns + 2):
                    kb.append(lines[i].strip("\n"))
                break
        input_file.close()
        return queries, kb

    except IOError:
        fo = open(output_file, 'w')
        fo.write("File not found: {}".format(fin))
        fo.close()
        sys.exit()


def parseKB(kb):
    negativeKB = dict()
    positiveKB = dict()

    for item in kb:
        data = item.split('|')
        for i in data:
            i = i.replace(' ', '')
            if i[0] == '~':
                b = i[1:]
                b = b.partition("(")[0]
                try:
                    negativeKB[b].append(item)
                except KeyError:
                    negativeKB[b] = [item]
            else:
                i = i.partition("(")[0]
                try:
                    positiveKB[i].append(item)
                except KeyError:
                    positiveKB[i] = [item]

    return negativeKB, positiveKB


def extract_constants(query):
    variable = re.search(r'\((.*?)\)', query).group(1)
    return variable


# Checks if a variable exists
def checkSentence(kb):
    if "|" in kb:
        return False
    constants = re.search(r'\((.*?)\)', kb).group(1)
    constantsList = constants.split(",")
    for val in constantsList:
        if val[0].isupper():
            continue
        else:
            return False
    return True


def isNegative(query):
    return query[0] == '~'


def getRemoveQueries(query, query_temp, sentence):
    if query[0] != '~':
        return sentence[1:], "~" + query_temp
    else:
        return "~" + sentence, query_temp[1:]


def unification(query, left_over, positiveKB, negativeKB, can_simplyfy):
    predicate = query.split('(')[0]

    value = None

    if query[0] != '~':
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
        if " |  | " in news1:
            news2 = news1.replace(" |  | ", " | ")
            return 1, news2
        elif news1[:3] == " | ":
            news2 = news1[3:]
            return 1, news2
        elif news1[-3:] == " | ":
            news2 = news1[:-3]
            return 1, news2
        else:
            return 1, news1
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
                if j[0].isupper() and queryArgsList[count][0].islower():
                    query = replaceVariableWithConstant(queryArgsList[count], query, j)
                    flag = True
                    count += 1
                elif j[0].islower() and queryArgsList[count][0].isupper():
                    sentence = replaceVariableWithConstant(j, sentence, queryArgsList[count])
                    flag = True
                    count += 1
                elif j[0].isupper() and queryArgsList[count][0].isupper():
                    flag = (j == queryArgsList[count])
                    if flag:
                        count += 1
                    else:
                        break
                elif j[0].islower() and queryArgsList[count][0].islower():
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
    output_file = "output.txt"
    fo = open(output_file, 'w')
    query_list, sentences = get_input()
    negativeKB, positiveKB = parseKB(sentences)

    can_simplyfy = []
    for a in sentences:
        if checkSentence(a):
            can_simplyfy.append(a)

    for query in query_list:
        if query[0] == '~':
            new_query = query[1:]
            if unification(new_query, new_query, positiveKB, negativeKB, can_simplyfy):
                fo.write("TRUE" + "\n")
            else:
                fo.write("FALSE" + "\n")

        else:
            new_query = "~" + query
            if unification(new_query, new_query, positiveKB, negativeKB, can_simplyfy):
                fo.write("TRUE" + "\n")
            else:
                fo.write("FALSE" + "\n")
    fo.close()


if __name__ == '__main__':
    main()
