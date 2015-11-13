'''
Created on Jan 27, 2014

@author: nando
'''

from Types import Argument, Predicate, Identifier,\
                  AssignationExpression, BooleanExpression,\
                  ArithmeticExpression

import random, string, re

# This variable is used to generate the uniqueIds of the predicates.
# In case of being True a random generated text chunk will be added
# to the uniqueId representing the predicate.
GENERATE_RANDOM_CHUNK=True

def random_generator(size=6, chars=string.ascii_letters+string.digits):
    return ''.join(random.choice(chars) for _ in range(size))

def removeRuleSpaces(rule):
    return "".join([x for x in rule if x != " " and x != " \t" and x != "\n"])

def makeArgument(arg):
    try:
        return Argument('constant', int(arg))
    except ValueError:
        return Argument('variable', arg)

# This function is used to parse assignation expressions of the kind A = B + C
# The grammar is:
#   VARIABLE_OR_NUMBER ::= VARIABLE | NUMBER
#   ARITHMETIC_EXPRESSION ::= VARIABLE_OR_NUMBER ARITHMETIC_OPERATOR
#                             VARIABLE_OR_NUMBER
#   ASSIGNATION_EXPRESSION ::= VARIABLE_OR_NUMBER EQUAL_OPERATOR
#                              ARITHMETIC_EXPRESSION
# Clousure added to compute the compilation of the regexes only once.
# THIS FUNCTION IS DEPRECATED BY NOW!!!. May be used again on future
# extensions.
def clousure_get_assignation_expression():
    VAR = '[A-Za-z]+'
    NUMBER = '[0-9]+'
    VAR_OR_NUMBER = "(" + VAR + "|" + NUMBER + ")"
    EXPRESSION = "("+ VAR + ")" + "=" + VAR_OR_NUMBER + r"([\+\-\*/])" + VAR_OR_NUMBER
    assignation = re.compile(EXPRESSION)
    def _(rule, start_position):
        match = assignation.match(rule[start_position:])
        if match == None:
            return None, start_position

        left_side = match.groups()[0]
        operator = match.groups()[2]
        right_side_arguments = []
        for arg in match.groups()[1::2]:
            try:
                right_side_arguments.append(Argument('constant', int(arg)))
            except ValueError:
                right_side_arguments.append(Argument('variable', arg))

        return AssignationExpression('assignation', Argument('variable', left_side),
                                     right_side_arguments, operator),\
               start_position + match.end()
    return _
get_assignation_expression = clousure_get_assignation_expression()

# This function is used to parse boolean expressions of the kind
# A < B where A and B can be arithmetic expressions or arguments.
# The grammar is:
#  VARIABLE_OR_NUMBER ::= VARIABLE | NUMBER
#  ARITHMETIC_EXPRESSION ::= VARIABLE_OR_NUMBER ARITHMETIC_OPERATOR
#                            VARIABLE_OR_NUMBER
#  EXPRESSION ::= VARIABLE_OR_NUMBER | ARITHMETIC_EXPRESSION
#  BOOLEAN_EXPRESSION ::= EXPRESSION BOOLEAN_OPERATOR EXPRESSION
# Clousure added to compute the compilation of the regexes only once.
# Please take in mind that arithmetic expressions can't be nested (Y+1+N)
# will not be parsed.
def clousure_get_boolean_expression():
    VAR = '[A-Z][A-Za-z0-9_]*'
    NUMBER = '[0-9]+'
    VAR_OR_NUMBER = "(" + VAR + "|" + NUMBER + ")"
    EXPRESSION = VAR_OR_NUMBER + r"([\+\-\*/\%])" +\
                 VAR_OR_NUMBER
    EXPRESSION_WITH_PARENTHESES = "\(" + VAR_OR_NUMBER +\
            r"([\+\-\*/\%])" + VAR_OR_NUMBER + "\)"
    EXPRESSION_SIDE = "([A-Za-z0-9\+\*\-/\(\)\%]+)"
    BOOLEAN_EXPRESSION = EXPRESSION_SIDE +\
                         "(==|<|>|<=|>=|!=)" +\
                         EXPRESSION_SIDE
    arg = re.compile(VAR_OR_NUMBER + "$")
    expression = re.compile(EXPRESSION + "$")
    expression_with_parentheses = re.compile(EXPRESSION_WITH_PARENTHESES)
    boolean = re.compile(BOOLEAN_EXPRESSION)
    def _(rule, start_position):
        match = boolean.match(rule[start_position:])
        if match == None:
            return None, start_position

        left_side, operator, right_side = match.groups()
        
        left_argument = None
        if (arg.match(left_side)):
            left_argument = makeArgument(left_side)
        elif expression.match(left_side):
            arg1, op, arg2 = expression.match(left_side).groups()
            left_argument = ArithmeticExpression((makeArgument(arg1), makeArgument(arg2)),
                                                 op)
        elif expression_with_parentheses.match(left_side):
            arg1, op, arg2 = expression_with_parentheses.match(left_side).groups()
            left_argument = ArithmeticExpression((makeArgument(arg1), makeArgument(arg2)),
                                                 op)
        else:
            return None, start_position
        
        right_argument = None
        if (arg.match(right_side)):
            right_argument = makeArgument(right_side)
        elif expression.match(right_side):
            arg1, op, arg2 = expression.match(right_side).groups()
            right_argument = ArithmeticExpression((makeArgument(arg1), makeArgument(arg2)),
                                                   op)
        elif expression_with_parentheses.match(right_side):
            arg1, op, arg2 = expression_with_parentheses.match(right_side).groups()
            right_argument = ArithmeticExpression((makeArgument(arg1), makeArgument(arg2)),
                                                 op)
        else:
            return None, start_position
        
        return BooleanExpression('boolean', (left_argument, right_argument), operator),\
               start_position + match.end()
    return _
get_boolean_expression = clousure_get_boolean_expression()

# Clousure used to avoid adding the uniqueIds dictionary as a global variable.
def clousure_get_predicate():
    uniqueIds = {}
    NEGATION_CHAR = '~?'
    NAME = NEGATION_CHAR + '[a-zA-Z][A-Za-z0-9_]*'
    name_match = re.compile(NAME + "$")
    def _(rule, start_position):
        """ This function is used to parse a predicate of the 
        form NAME(VAR1,...,VARN) from the start position"""
        
        # Get the identifier name of the predicate. If the identifier 
        # name is not something valid stop parsing it as a Predicate.
        end_name_position = rule.find('(', start_position)
        if (end_name_position == -1) or (end_name_position == start_position):
            return None, start_position

        name = rule[start_position:end_name_position]
        if name_match.match(name) == None:
            return None, start_position
        
        is_negated = False
        # Check if the predicated is negated
        if name[0] == '~':
            is_negated = True
            name = name[1:]
        
        if name in uniqueIds:
            uniqueId = uniqueIds[name]
        else:
            if GENERATE_RANDOM_CHUNK:
                uniqueId = name + '_' + random_generator(5)
            else:
                uniqueId = name
                
            uniqueIds[name] = uniqueId

        last_var_position = rule.find(')', end_name_position+1)
        if end_name_position == -1:
            return None, start_position
        
        if rule.find('(', end_name_position+1, last_var_position) != -1:
            return None, start_position
        
        #variables = rule[end_name_position+1:last_var_position].split(",")
        # Here we check if the 
        string_arguments = rule[end_name_position+1:last_var_position].split(",")
        arguments = []
        for arg in string_arguments:
            try:
                arguments.append(Argument('constant', int(arg)))
            except ValueError:
                arguments.append(Argument('variable', arg))
        #print arguments
            
        #return (name, variables), last_var_position+1
        return Predicate(Identifier(name, uniqueId), is_negated, arguments), last_var_position+1
    return _
get_predicate = clousure_get_predicate()

def get_head_separator(rule, start_position):
    """ Checks that from the starting position what we have is the head rule
    separator """
    if start_position+2 >= len(rule) or\
       rule[start_position:start_position+2] != ':-':
        return False, start_position
    else:
        return True, start_position+2
    
def get_predicate_seaparator(rule, start_position):
    """ Checks that from the starting position what we have is the body rule
    predicate separator """
    if start_position+1 >= len(rule) or rule[start_position] != ',':
        return False, start_position
    else:
        return True, start_position+1
    
def parseRule(rule, check_restricted=False):
    """This functions parses a rule. It removes all the spaces of the given
    rule and parses it returning a tuple of two elements, containing the 
    head as first element and a list of tuples representing the body as 
    second element. Both the head and body elements are tuples containing a 
    string representing the predicate name as a first element, and a list of 
    strings representing the variables as a second element""" 
    rule = removeRuleSpaces(rule)

    # Get the predicate head    
    head, position = get_predicate(rule, 0)
    if head == None:
        raise ValueError('Incorrect head')
    
    # Check that the next we have in the rule is the separator
    v, position = get_head_separator(rule, position)
    if not v:
        raise ValueError('Head separator not found')
    
    parser_body_elements = [get_predicate, get_boolean_expression]

    # Get the body.
    body = []
    # We don't check if we are parsing a restricted body or not.
    # That is handled later on at BuildRulesTables.
    while True:
        # We check if the next element is a predicate or one of
        # the supported expressions (assignment or boolean)
        # otherwise we rise an error.
        element_parsed = False
        for parser_element in parser_body_elements:
            element, position = parser_element(rule, position)
            if element != None:
                element_parsed = True
                body.append(element)
                break


        if element_parsed == False:
            raise ValueError('Incorrect body')

        # Check if arrived to the end of the rule in an incorrect position
        if position >= len(rule):
            raise ValueError('Unfishined rule')
        
        # Is this the end of the rule?
        if rule[position] == '.':
            break
        
        # Get the separator for the second predicate.
        v, position = get_predicate_seaparator(rule, position)
        if v == False:
            raise ValueError('Incorrect body')

    # Check, if we have to, that we don't have more than two hypothesis in 
    # the rule
    if check_restricted and rule[position] != '.':
        raise ValueError('The body of a rule can at max have only two hypothesis')
    
    return (head, body)