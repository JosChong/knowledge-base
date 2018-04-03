import read, logic

facts, rules = read.read_tokenize("statements.txt")

kb = logic.kb()
for f in facts:
    logic.KB_assert(kb, f)
for r in rules:
    logic.KB_assert(kb, r)

for f in kb.facts:
    print(f)
for r in kb.rules:
    print(r)
