# These are the wrapper functions that connect the TestLogic code to your code
# The stubs are currently aimed at my version of the assignment. You will need to 
# redirect them to yours

# Tests to see if an input is a statement (as opposed to a rule)

def factq(element):
    return type(element[0]) is str 

# KB_assert Asserts a statement or a rule to a knowledge base. It invokes different code if it is one or the other.
# New facts and rules can trigger inference

def KB_assert(kb, assertion):
    if factq(assertion):
        kb.KB_assert_fact(assertion)
    else:
        kb.KB_assert_rule(assertion)

# KB_ask queries the knowledge base to check if a statement is true. 
            
def KB_ask(kb, query):
    if factq(query):
        return kb.KB_ask(query)
    else:
        return kb.KB_ask_rule(query)   

# KB_why shows us the supports for a statement

def KB_why(kb, query):
    if factq(query):
        kb.KB_why(query)   

# KB_retract removes a statement from the knowledge base and then all other facts and rules that 
# it supports
 
def KB_retract(kb, statement):
    if factq(statement):
        kb.KB_retract(statement)  

# KB_ask_plus queries the knowledge base to check if a list of statements are true. 
 
def KB_ask_plus(kb, query):
    return kb.KB_ask_plus(query) 