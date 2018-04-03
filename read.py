# read_statements takes the name of a file, reads it in and tokenizes the statements and
# rules in that file.

def read_tokenize(file):
    tokenized_facts =[]
    tokenized_rules =[]
    file = open(file, "r")
    elements = []
    current = ""
    for line in file:
        if line[0:5] in ("fact:","rule:"):
            elements.append(current)
            current = line.rstrip()
        else:
            current = current + " " + line.rstrip()
    elements.append(current)
    for e in elements:
        if e[0:5] == "fact:":
            e = e[5:].replace(")","").replace("(","").rstrip().strip().split()
            tokenized_facts.append(e)
        if e[0:5] == "rule:":
            e = e[5:].split("->")
            rhs = e[1].replace(")","").replace("(","").rstrip().strip().split()
            lhs = e[0].rstrip(") ").strip("( ").replace("(","").split(")")
            lhs = list(map(lambda x: x.rstrip().strip().split(), lhs))
            tokenized_rules.append((lhs,rhs))
    file.close()
    return tokenized_facts, tokenized_rules


def read_from_input(message):
    return raw_input(message + " ")

def get_new_fact():
    e = read_from_input("Please type in a new fact or rule you want to add to the KB: ")
    if e[0:5] == "fact:":
        e = e[5:].replace(")","").replace("(","").rstrip().strip().split()
        return e
    if e[0:5] == "rule:":
        e = e[5:].split("->")
        rhs = e[1].replace(")","").replace("(","").rstrip().strip().split()
        lhs = e[0].rstrip(") ").strip("( ").replace("(","").split(")")
        lhs = list(map(lambda x: x.rstrip().strip().split(), lhs))
        return [lhs,rhs]


def get_new_text():
    e = read_from_input("Please type in a statement: ")
    return list(map(lambda x: filter(str.isalnum, x), e.split(" ")))
