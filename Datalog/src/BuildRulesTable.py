'''
Created on Jul 10, 2013

@author: nando
'''

import sys
import logging

from Utils import LogicRule, PredicateTypes
from collections import defaultdict

def addRuleDependencyToGraph(graph, head, body):
    for pred in body:
        #if not graph.has_key(pred):
        #    graph[pred] = dict()
        graph[pred][head] = 0

def removeRuleSpaces(rule):
    return "".join([x for x in rule if x != " " and x != " \t" and x != "\n"])

def get_predicate(rule, start_position):
    """ This function is used to parse a predicate of the 
    form NAME(VAR1,...,VARN) from the start position"""
    
    end_name_position = rule.find('(', start_position)
    if end_name_position == -1:
        return None, start_position
    name = rule[start_position:end_name_position]
    last_var_position = rule.find(')', end_name_position+1)
    if end_name_position == -1:
        return None, start_position
    
    if rule.find('(', end_name_position+1, last_var_position) != -1:
        return None, start_position
    
    variables = rule[end_name_position+1:last_var_position].split(",")
    return (name, variables), last_var_position+1

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
    
def parseRule(rule):
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
    
    # Get the body. Here we can only have two predicates
    body = []
    for _ in xrange(2):
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

    # Check that we don't have more than three hypothesis in the rule
    if rule[position] != '.':
        raise ValueError('The body of a rule can at max have only two hypothesis')
    
    return (head, body)
        
         
def buildRulesTable(filename, test=False):
    """This function is in charge to build the rules table, the rules table
       is a data structure containing a description for all the logical
       rules of the program, a description for what a logical rule data type
       is can be found in the Utils.py file. This function also returns the
       dependency graph. A dependency graph is a dict containing the dependency
       information in a bottom-up fashion. The predicateTypes is a tuple which
       separates the set of intenstional and extensional."""    
    if test: f = filename
    else : f = open(filename, 'r')
    
    dependency_graph = defaultdict(lambda: defaultdict(int))
    
    head_preds = set() 
    body_preds = set() 
    rulesTable = []
    for line_no, line in enumerate(f, start=1):
        if line[0] == '\n': continue
        
        try:
            rule = parseRule(line)
        except ValueError as v:
            if not test:
                logging.error('Parsing:%s:Line:%i', filename, line_no)
                logging.error('Parsing:%s', v.message)

            sys.exit(0)
            
        body_predicates = [body_pred[0] for body_pred in rule[1]]
        head_preds.add(rule[0][0])
        body_preds.update(body_predicates)
        addRuleDependencyToGraph(dependency_graph, rule[0][0], body_predicates)
        rulesTable.append(LogicRule(rule[0], rule[1], len(rule[1]), line_no+1, line))
            
    f.close()
    return (rulesTable, PredicateTypes(head_preds, body_preds.difference(head_preds)), dependency_graph)

