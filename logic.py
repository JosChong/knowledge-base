import copy, Queue

class kb(object):
    def __init__(self):
        self.facts = []
        self.rules = []

    def __str__(self):
        return "KB\n" + "# of facts: " + str(len(self.facts)) + "\n# of rules: " + str(len(self.rules)) + "\n"

    def KB_assert_fact(self, statement):
        new_fact = fact(statement)
        print "Asserting " + str(new_fact) + "\n"
        contained_fact = self.contains_fact(new_fact)
        if not contained_fact:
            self.facts.append(new_fact)
            self.infer_from_fact(new_fact)
        else:
            contained_fact.asserted = True

    def KB_assert_rule(self, statement):
        new_rule = rule(statement)
        print "Asserting " + str(new_rule) + "\n"
        contained_rule = self.contains_rule(new_rule)
        if not contained_rule:
            self.rules.append(new_rule)
            self.infer_from_rule(new_rule)
        else:
            contained_rule.asserted = True

    def KB_retract(self, statement):
        contained_fact = self.contains_fact(fact(statement))
        if contained_fact and contained_fact.asserted:
            print "Retracting " + str(contained_fact) + "\n"
            if not contained_fact.supportedBy:
                for f in contained_fact.factsSupported:
                    print "Removing support for " + str(f) + "\n"
                    f.supportedBy.remove(contained_fact)
                    if not f.asserted:
                        self.KB_retract_fact(f)
                for r in contained_fact.rulesSupported:
                    print "Removing support for " + str(r) + "\n"
                    r.supportedBy.remove(contained_fact)
                    if not r.asserted:
                        self.KB_retract_rule(r)
                print "Removing " + str(contained_fact) + "\n"
                self.facts.remove(contained_fact)
            else:
                contained_fact.asserted = False

    def KB_retract_fact(self, fact):
        if len(fact.supportedBy) <= 1:
            for f in fact.factsSupported:
                print "Removing support for " + str(f) + "\n"
                f.supportedBy.remove(fact)
                if not f.asserted:
                    self.KB_retract_fact(f)
            for r in fact.rulesSupported:
                print "Removing support for " + str(r) + "\n"
                r.supportedBy.remove(fact)
                if not r.asserted:
                    self.KB_retract_rule(r)
            print "Removing " + str(fact) + "\n"
            self.facts.remove(fact)

    def KB_retract_rule(self, rule):
        if len(rule.supportedBy) <= 1:
            for f in rule.factsSupported:
                f.supportedBy.remove(rule)
                if not f.asserted:
                    self.KB_retract_fact(f)
            for r in rule.rulesSupported:
                r.supportedBy.remove(rule)
                if not r.asserted:
                    self.KB_retract_rule(r)
            print "Removing " + str(rule) + "\n"
            self.rules.remove(rule)

    def KB_ask(self, query):
        return filter(lambda x: x, map(lambda x: match(x.statement, query), self.facts))

    def KB_ask_rule(self, query):
        return

    def KB_ask_plus(self, queries):
        bindings_list = [bindings()]
        for query in queries:
            new_bindings_list = []
            for bindings_set in bindings_list:
                new_bindings = filter(lambda x: x, map(lambda x: match(x.statement, query, copy.deepcopy(bindings_set)), self.facts))
                new_bindings_list += new_bindings
            bindings_list = new_bindings_list
        return bindings_list

    def KB_why(self, query):
        contained_fact = self.contains_fact(fact(query))
        if contained_fact:
            print "Explaining " + str(contained_fact)
            inference_tree = Queue.Queue()
            inference_tree.put((0, contained_fact, contained_fact.asserted))
            if not contained_fact.asserted:
                for s in contained_fact.supportedBy:
                    self.KB_why_helper(s, inference_tree, 1)
            self.KB_why_print(inference_tree)

    def KB_why_helper(self, statement, inference_tree, level):
        inference_tree.put((level, statement, statement.asserted))
        if not statement.asserted:
            for s in statement.supportedBy:
                self.KB_why_helper(s, inference_tree, level + 1)

    def KB_why_print(self, inference_tree):
        while not inference_tree.empty():
            step = inference_tree.get()
            for x in range(step[0]):
                print "---",
            if not step[2]:
                print str(step[1])
            else:
                print str(step[1]) + " Asserted!"
        print "\n"

    def infer_from_fact(self, base_fact):
        for r in self.rules:
            bindings = match(base_fact.statement, r.lhs[0])
            if bindings:
                if len(r.lhs) != 1:
                    new_lhs = instantiate_list(r.lhs[1:], bindings)
                    new_rhs = instantiate(r.rhs, bindings)
                    new_rule = rule((new_lhs, new_rhs), (base_fact, r))
                    contained_rule = self.contains_rule(new_rule)
                    if not contained_rule:
                        print "Inferring " + str(new_rule) + " from " + str(base_fact) + " & " + str(r) + "\n"
                        base_fact.rulesSupported.append(new_rule)
                        r.rulesSupported.append(new_rule)
                        self.rules.append(new_rule)
                        self.infer_from_rule(new_rule)
                    else:
                        base_fact.rulesSupported.append(contained_rule)
                        contained_rule.supportedBy.append(base_fact)
                        if contained_rule not in r.rulesSupported:
                            r.rulesSupported.append(contained_rule)
                        if r not in contained_rule.supportedBy:
                            contained_rule.supportedBy.append(r)
                else:
                    new_statement = instantiate(r.rhs, bindings)
                    new_fact = fact(new_statement, (base_fact, r))
                    contained_fact = self.contains_fact(new_fact)
                    if not contained_fact:
                        print "Inferring " + str(new_fact) + " from " + str(base_fact) + " & " + str(r) + "\n"
                        base_fact.factsSupported.append(new_fact)
                        r.factsSupported.append(new_fact)
                        self.facts.append(new_fact)
                        self.infer_from_fact(new_fact)
                    else:
                        base_fact.factsSupported.append(contained_fact)
                        contained_fact.supportedBy.append(base_fact)
                        if contained_fact not in r.factsSupported:
                            r.factsSupported.append(contained_fact)
                        if r not in contained_fact.supportedBy:
                            contained_fact.supportedBy.append(r)

    def infer_from_rule(self, base_rule):
        for f in self.facts:
            bindings = match(f.statement, base_rule.lhs[0])
            if bindings:
                if len(base_rule.lhs) != 1:
                    new_lhs = instantiate_list(base_rule.lhs[1:], bindings)
                    new_rhs = instantiate(base_rule.rhs, bindings)
                    new_rule = rule((new_lhs, new_rhs), (f, base_rule))
                    contained_rule = self.contains_rule(new_rule)
                    if not contained_rule:
                        print "Inferring " + str(new_rule) + " from " + str(f) + " & " + str(base_rule) + "\n"
                        f.rulesSupported.append(new_rule)
                        base_rule.rulesSupported.append(new_rule)
                        self.rules.append(new_rule)
                        self.infer_from_rule(new_rule)
                    else:
                        base_rule.rulesSupported.append(contained_rule)
                        contained_rule.supportedBy.append(base_rule)
                        if contained_rule not in f.rulesSupported:
                            f.rulesSupported.append(contained_rule)
                        if f not in contained_rule.supportedBy:
                            contained_rule.supportedBy.append(f)
                else:
                    new_statement = instantiate(base_rule.rhs, bindings)
                    new_fact = fact(new_statement, (f, base_rule))
                    contained_fact = self.contains_fact(new_fact)
                    if not contained_fact:
                        print "Inferring " + str(new_fact) + " from " + str(f) + " & " + str(base_rule) + "\n"
                        f.factsSupported.append(new_fact)
                        base_rule.factsSupported.append(new_fact)
                        self.facts.append(new_fact)
                        self.infer_from_fact(new_fact)
                    else:
                        base_rule.factsSupported.append(contained_fact)
                        contained_fact.supportedBy.append(base_rule)
                        if contained_fact not in f.factsSupported:
                            f.factsSupported.append(contained_fact)
                        if f not in contained_fact.supportedBy:
                            contained_fact.supportedBy.append(f)

    def contains_fact(self, fact):
        for f in self.facts:
            if f.statement == fact.statement:
                return f
        return False

    def contains_rule(self, rule):
        for r in self.rules:
            if r.lhs == rule.lhs and r.rhs == rule.rhs:
                return r
        return False

class fact(object):
    def __init__(self, statement, supportedBy = []):
        self.statement = statement
        self.asserted = (supportedBy == [])
        self.supportedBy = list(supportedBy)
        self.factsSupported = []
        self.rulesSupported = []

    def __str__(self):
        return "fact: " + str(self.statement)

class rule(object):
    def __init__(self, rule, supportedBy = []):
        self.lhs = rule[0]
        self.rhs = rule[1]
        self.asserted = (supportedBy == [])
        self.supportedBy = list(supportedBy)
        self.factsSupported = []
        self.rulesSupported = []

    def __str__(self):
        return "rule: " + str(self.lhs) + " -> " + str(self.rhs)

class bindings(object):
	def __init__(self):
		self.bindings = {}
		self.pretty = []

	def __str__(self):
		return str(self.pretty)

	def add_binding(self, variable, value):
		self.bindings[variable] = value
		self.pretty.append((variable.upper(), value))

	def binding_value(self, variable):
		if variable in self.bindings.keys():
			return self.bindings[variable]
		return variable

	def test_and_bind(self, variable, value):
		if variable in self.bindings.keys():
			if value == self.bindings[variable]:
				return True
			else:
				return False
		self.add_binding(variable, value)
		return True

def match(statement1, statement2, new_bindings = None):
    if new_bindings == None:
        new_bindings = bindings()
    if len(statement1) != len(statement2):
        return False
    if len(statement1) == 0:
        return new_bindings
    if var(statement2[0]):
        if not new_bindings.test_and_bind(statement2[0], statement1[0]):
            return False
    elif statement1[0] != statement2[0]:
        return False
    return match(statement1[1:], statement2[1:], new_bindings)

def instantiate(statement, bindings):
    return map(lambda s: bindings.binding_value(s), statement)

def instantiate_list(statements, bindings):
    return map(lambda statement: instantiate(statement, bindings), statements)

def var(term):
    return term[0] == "?"

def factq(element):
    return type(element[0]) is str

def KB_assert(kb, assertion):
    if factq(assertion):
        kb.KB_assert_fact(assertion)
    else:
        kb.KB_assert_rule(assertion)

def KB_retract(kb, statement):
    if factq(statement):
        kb.KB_retract(statement)

def KB_ask(kb, query):
    if factq(query):
        return kb.KB_ask(query)
    else:
        return kb.KB_ask_rule(query)

def KB_ask_plus(kb, query):
    return kb.KB_ask_plus(query)

def KB_why(kb, query):
    if factq(query):
        kb.KB_why(query)
