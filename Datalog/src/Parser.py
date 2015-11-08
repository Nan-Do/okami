'''
Created on Jan 27, 2014

@author: nando
'''

from Types import Argument, Predicate, Identifier,\
                  AssignationExpression, BooleanExpression

import random, string, re

# This variable is used to generate the uniqueIds of the predicates.
# In case of being True a random generated text chunk will be added
# to the uniqueId representing the predicate.
GENERATE_RANDOM_CHUNK=True

def random_generator(size=6, chars=string.ascii_letters+string.digits):
    return ''.join(random.choice(chars) for _ in range(size))

def removeRuleSpaces(rule):
    return "".join([x for x in rule if x != " " and x != " \t" and x != "\n"])

# This function is used to parse assignation expressions of the kind A = B + C
# The grammar is VAR = NUMBER|VARIABLE + [+-*/] + NUMBER|VARIABLE. Clousure added
# to compute the compilation of the regex only once.
def clousure_get_assignation_expression():
    VAR = '[A-Za-z]+'
    NUMBER = '[0-9]+'
    VAR_OR_NUMBER = "(" + VAR + "|" + NUMBER + ")"
    EXPRESSION = "("+ VAR + ")" + "=" + VAR_OR_NUMBER + r"([\+-\\\*])" + VAR_OR_NUMBER
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

# This function is used to parse boolean expressions of the kind A < B
# The grammar is NUMBER|VARIABLE < NUMBER|VARIABLE. Clousure added
# to compute the compilation of the regex only once.
def clousure_get_boolean_expression():
    VAR = '[A-Za-z]+'
    NUMBER = '[0-9]+'
    VAR_OR_NUMBER = "(" + VAR + "|" + NUMBER + ")"
    EXPRESSION = VAR_OR_NUMBER + "(==|<|>|<=|>=|!=)" + VAR_OR_NUMBER
    boolean = re.compile(EXPRESSION)
    def _(rule, start_position):
        match = boolean.match(rule[start_position:])
        if match == None:
            return None, start_position

        #return match.groups(), start_position + match.end()
        operator = match.groups()[1]
        right_side_arguments = []
        for arg in match.groups()[0::2]:
            try:
                right_side_arguments.append(Argument('constant', int(arg)))
            except ValueError:
                right_side_arguments.append(Argument('variable', arg))

        return BooleanExpression('boolean', right_side_arguments, operator),\
               start_position + match.end()
    return _
get_boolean_expression = clousure_get_boolean_expression()

# Clousure used to avoid adding the uniqueIds dictionary as a global variable.
def clousure_get_predicate():
    uniqueIds = {}
    def _(rule, start_position):
        """ This function is used to parse a predicate of the 
        form NAME(VAR1,...,VARN) from the start position"""
        
        end_name_position = rule.find('(', start_position)
        if end_name_position == -1:
            return None, start_position
        name = rule[start_position:end_name_position]
        
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
    
    parser_body_elements = [get_predicate, get_assignation_expression,
                            get_boolean_expression]

    # Get the body.
    body = []
    # We don't check if we are parsing a restricted body or not.
    # TODO: Check if we are dealing with a restricted body and act
    # appropriately if we have to generate code for it
    while True:
        # We check if the next element is a predicate or one of
        # the supported expressions (assignment or boolean)
        # otherwise we rise an error.
        element_parsed = False
        for parser_element in parser_body_elements:
            element, position = parser_element(rule, position)
            if element == None:
                continue
            element_parsed = True
            body.append(element)

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