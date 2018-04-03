# Binding

# A single binding is a pair of variable/value
# A set or list of bindings defines the constraints on match between two statements
# Once defined, you can add a new binding pair, get the value associated with a variable
# and test to see if a variable matches a constant.
# If a variable is bound then it will only match the same constant
# If it is unbound, then it will match and the binding is added

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
		return False

	def test_and_bind(self, variable, value):
		if variable in self.bindings.keys():
			if value == self.bindings[variable]:
				return True
			else:
				return False
		self.add_binding(variable, value)
		return True

# Match tests two elements against each the to see if they match.
# Constants match each other
# Unbound variables match constants and are bound to them
# Bound variables match against a constant if they are bound to the same constant

def match(statement1, statement2, mybindings = None):
	if mybindings == None:
        mybindings = bindings()
	if len(statement1) != len(statement2):
		return False
	if len(statement1) == 0:
		return bindings
	if varq(statement2[0]):
		if not bindings.test_and_bind(statement2[0], statement1[0]):
			return False
	elif statement1[0] != statement2[0]:
		return False
	return match(statement1[1:], statement2[1:], bindings)
