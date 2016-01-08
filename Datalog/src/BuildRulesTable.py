'''
Created on Jul 10, 2013

@author: nando
'''

import sys
import logging

from collections import defaultdict

from Parser import parseRule
from Types import LogicRule, PredicateTypes, Predicate, Argument
from Types import AssignationExpression, BooleanExpression
from Types import ArithmeticExpression


def addRuleDependencyToGraph(graph, head, body):
    for pred in body:
        #if not graph.has_key(pred):
        #    graph[pred] = dict()
        graph[pred][head] = 0

def logError(filename, line_no, error_type, error_message):
    logging.error('Analyzing:%s:Line:%i', filename, line_no)
    if error_type:
        logging.error('%s:%s', error_type, error_message)
    else:
        logging.error('%s', error_message)

# This function checks if a rule is unsafe. If a rule is unsafe can't be 
# evaluated.
def isAnUnsafeRule(head, body, assignations):
    vars_head = set(x.value for x in head.arguments if x.type == 'variable' )
    vars_body = set()
    
    if len(body) == 1:
        # Check that all the variables of the body appear on the head
        vars_body |= set(x.value for x in body[0].arguments if x.type == 'variable')
        
    elif len(body) == 2:
        vars_body |= set(x.value for x in body[0].arguments if x.type == 'variable')
        vars_body |= set(x.value for x in body[1].arguments if x.type == 'variable')
        
    if assignations:
        vars_body |= set(a.leftArgument.value for a in assignations)
            
    if not vars_head.issubset(vars_body):
            return True

    return False


def checkLeftSideVariableOnAssignationsAppearOnTheHead(head, assignation):
    vars_head = set(x.value for x in head.arguments if x.type == 'variable')
    
    if assignation.leftArgument.value in vars_head:
        return True
    
    return False


def checkRightSideVariablesOnAssignationsAppearOnTheBody(predicates_of_the_body, assignation):
    if isinstance(assignation.rightArgument, ArithmeticExpression):
        assignation_vars = set(argument.value for argument in assignation.rightArgument.arguments
                                                    if argument.type == 'variable')
    else:
        assignation_vars = set(assignation.rightArgument.value)
                   
    predicate_vars = set([y.value for x in predicates_of_the_body
                                  for y in x.arguments if y.type == 'variable'])
    
    if assignation_vars.issubset(predicate_vars):
        return True
    
    return False


def checkBooleanExpressionVariablesAppearOnTheBody(predicates_of_the_body, boolean):
    boolean_vars = set()
    for argument in boolean.arguments:
        if isinstance(argument, Argument) and argument.type == 'variable':
            boolean_vars.add(argument.value)
        elif isinstance(argument, ArithmeticExpression):
            boolean_vars.update(set([x.value for x in argument.arguments
                                               if x.type == 'variable']))

    predicate_vars = set([y.value for x in predicates_of_the_body
                                  for y in x.arguments if y.type == 'variable'])
    
    if boolean_vars.issubset(predicate_vars):
        return True
    
    return False


def buildRulesTable(filename, test=False):
    """This function is in charge to build the rules table, the rules table
       is a data structure containing a description for all the logical
       rules of the program, a description for what a logical rule data type
       is can be found in the Utils.py file. This function also returns the
       dependency graph. A dependency graph is a dict containing the dependency
       information in a bottom-up fashion. The predicateTypes is a tuple which
       separates the set of intenstional and extensional."""
    # This line is to handle testing properly.
    # When we are testing we pass a stream otherwise we pass the file name.
    # We do this as the filename is handled (opened and closed) inside this 
    # function.   
    if test: f = filename
    else : f = open(filename, 'r')
    
    dependency_graph = defaultdict(lambda: defaultdict(int))
    
    # Dictionary to from predicate to its length to check we don't redefine its definition
    preds_to_length = dict()
    
    head_preds_ids = set() 
    body_preds_ids = set()
    negated_preds = set()
    rulesTable = []
    for line_no, line in enumerate(f, start=1):
        if line[0] == '\n': continue
        
        try:
            (head, body) = parseRule(line, check_restricted=True)
        except ValueError as v:
            if not test:
                logError(filename,
                         line_no,
                         'Parsing',
                         v.message)
            sys.exit(0)
        
        # Obtain the different elements that compose the body of the rule.
        predicates = [x for x in body if isinstance(x, Predicate) and not x.negated]
        negated_predicates = [x for x in body if isinstance(x, Predicate) and x.negated]
        assignation_expressions = [x for x in body if isinstance(x, AssignationExpression)]
        boolean_expressions = [x for x in body if isinstance(x, BooleanExpression)]
        
        body_predicates_ids = [predicate.id for predicate in predicates]
        negated_predicate_ids = [neg_pred.id for neg_pred in negated_predicates]
        
        has_negated_predicates = (len(negated_predicate_ids) != 0)
        
        # Start for semantic error on the logical rules:
        # These errors can be found on the predicates or the expressions
        if len(predicates) == 0:
            logError(filename,
                     line_no,
                     'Parsing',
                     'Rules are required to have at least one predicate')
            sys.exit(0)
            
        if len(predicates) > 2:
            logError(filename,
                     line_no,
                     'Parsing',
                     'Rules can\'t contain more than two predicates')
            sys.exit(0)
           
        # Check that we are not redefining a predicate 
        if head.id not in preds_to_length:
            preds_to_length[head.id] = len(head.arguments)
        elif len(head.arguments) != preds_to_length[head.id]:
                logError(filename,
                     line_no,
                     None,
                     'Head of the rule redefines a predicate:' + head.id.name)
                sys.exit(0)
        for body_predicate in [x for x in body if isinstance(x, Predicate)]:
            if body_predicate.id not in preds_to_length:
                preds_to_length[body_predicate.id] = len(body_predicate.arguments)
            elif len(body_predicate.arguments) != preds_to_length[body_predicate.id]:
                logError(filename,
                     line_no,
                     None,
                     'Body of the rule redefines a predicate:' + body_predicate.id.name )
                sys.exit(0)
        
        # Check that the assignation expressions are properly defined
        for assignation_expression in assignation_expressions:
            if not checkLeftSideVariableOnAssignationsAppearOnTheHead(head, assignation_expression):
                logError(filename,
                         line_no,
                         None,
                         'The variable on the left side of the assignation doesn\'t ' +
                         'appear on head of the rule')
                sys.exit(0)
                
            if not checkRightSideVariablesOnAssignationsAppearOnTheBody(predicates, assignation_expression):
                logError(filename,
                         line_no,
                         None,
                         'A variable on the right side of the assignation doesn\'t ' +
                         'appear on the body of the rule')
                sys.exit(0)
        
        # Check that the boolean expressions are properly defined        
        for boolean_expression in boolean_expressions:
            if not checkBooleanExpressionVariablesAppearOnTheBody(predicates, boolean_expression):
                logError(filename,
                         line_no,
                         None,
                         'All the variables of the boolean expressions ' +\
                         'must appear on one the predicates of the body')
                sys.exit(0)
                
        # Is it an unsafe rule?
        # Conditions to be an unsafe rule:
        #    - A variable on the head doesn't appear on the body
        if isAnUnsafeRule(head, predicates, assignation_expressions):
            logError(filename,
                     line_no,
                     None,
                     'All the variables of the head must appear on a body predicate ' + 
                     'or the left side of an assignation')
            sys.exit(0)
                

        # Check for errors regarding negated predicates
        body_variables = set([y.value for x in predicates
                                      for y in x.arguments
                                      if y.type == 'variable'])            
        for negated_predicate in negated_predicates:
            if negated_predicate.id in body_predicates_ids:
                logError(filename,
                     line_no,
                     None,
                     'Predicate "' + negated_predicate.id.name + '" appears both negated and non-negated')
                sys.exit(0)
                
            for argument in negated_predicate.arguments:
                if argument.type == 'variable' and argument.value not in body_variables:
                    logError(filename,
                             line_no,
                             None,
                             'Negated predicate "' + negated_predicate.id.name + '" contains the unmatched variable "' +
                             argument.value + '"')
                    sys.exit(0)

            
        # Required to build the dependency graph. It is a directed graph that has a node
        # for every predicate (we store the predicate identifiers) and an edge connecting
        # two nodes if one predicate appears on the body and another one in the head.
        # Negated predicates also count as a body predicate.
        head_preds_ids.add(head.id)
            
        body_preds_ids.update(body_predicates_ids)
        negated_preds.update(negated_predicate_ids)
        
        addRuleDependencyToGraph(dependency_graph, head.id, body_predicates_ids + negated_predicate_ids)
        
        rulesTable.append(LogicRule(head, body, len(predicates), has_negated_predicates, line_no+1, line))
            
    f.close()
    return (rulesTable, PredicateTypes(head_preds_ids, body_preds_ids.difference(head_preds_ids)), dependency_graph, negated_preds)

