'''
Created on Jul 10, 2013

@author: nando
'''

import sys
import logging

from Parser import parseRule
from Types import LogicRule, PredicateTypes
from collections import defaultdict

def addRuleDependencyToGraph(graph, head, body):
    for pred in body:
        #if not graph.has_key(pred):
        #    graph[pred] = dict()
        graph[pred][head] = 0
         
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
                logging.error('Parsing:%s:Line:%i', filename, line_no)
                logging.error('Parsing:%s', v.message)

            sys.exit(0)
            
        body_predicates_ids = [predicate.id for predicate in body]
        negated_predicate_ids = [predicate.id for predicate in body if predicate.negated]
        head_preds_ids.add(head.id)
        negated_preds.update(negated_predicate_ids)
        body_preds_ids.update(body_predicates_ids)
        addRuleDependencyToGraph(dependency_graph, head.id, body_predicates_ids)
        rulesTable.append(LogicRule(head, body, len(body), line_no+1, line))
            
    f.close()
    return (rulesTable, PredicateTypes(head_preds_ids, body_preds_ids.difference(head_preds_ids)), dependency_graph, negated_preds)

