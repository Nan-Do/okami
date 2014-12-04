'''
Created on Jan 27, 2014

@author: nando
'''

from itertools import repeat
from Types import Argument, Predicate

import random, string

def random_generator(size=6, chars=string.ascii_letters+string.digits):
    return ''.join(random.choice(chars) for _ in range(size))

def removeRuleSpaces(rule):
    return "".join([x for x in rule if x != " " and x != " \t" and x != "\n"])

def decorate_get_predicate():
    unique_ids = {}
    def get_predicate_function(rule, start_position):
        """ This function is used to parse a predicate of the 
        form NAME(VAR1,...,VARN) from the start position"""
        
        end_name_position = rule.find('(', start_position)
        if end_name_position == -1:
            return None, start_position
        name = rule[start_position:end_name_position]
        
        if name in unique_ids:
            unique_id = unique_ids[name]
        else:
            unique_id = name + '_' + random_generator(3)
            unique_ids[name] = unique_id

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
        return Predicate(name, unique_id, False, arguments), last_var_position+1
    return get_predicate_function
get_predicate = decorate_get_predicate()

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
    
    # Get the body.
    body = []
    # Check if we are parsing a restricted body or not
    if check_restricted:
        r = repeat(True, 2)
    else:
        r = repeat(True)
        
    for _ in r:
        body_element, position = get_predicate(rule, position)
        if body_element == None:
            raise ValueError('Incorrect body')
        body.append(body_element)
        
        # Check if arrived to the end of the rule in an incorrect position
        if position>=len(rule):
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
