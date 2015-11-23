'''
Created on Jan 27, 2014

@author: nando
'''

import sys
import logging

from Parser import parseRule
from Types import LogicRule, BooleanExpression
from DecomposingMethods import rightMostDecomposingMethod, leftMostDecomposingMethod,\
    commonVariablesDecomposingMethod, randomDecomposingMethod

#===============================================================================
# This module is used to decompose a Datalog program right now only the 
# decomposition starting from the left is supported it should suffice for most
# of the cases
#===============================================================================


def getDecomposerRuleMethod(method):
    buildingRulesAlgorithims = {'left' : leftMostDecomposingMethod,
                                'right': rightMostDecomposingMethod,
                                'random': randomDecomposingMethod,
                                'common': commonVariablesDecomposingMethod}
    
    if method not in buildingRulesAlgorithims:
        logging.error("{} is an unknown method to decompose the rules".format(method))
        raise ValueError 
    
    return buildingRulesAlgorithims[method]
    
def decomposeRulesFromFile(filename, method='random'):
    decomposeRule = getDecomposerRuleMethod(method)
    logging.info("Using method {}".format(method))
    
    f = open(filename, 'r')
    newRules = []
    
    for line_no, line in enumerate(f, start=1):
        if line[0] == '\n': continue
        
        try:
            rule = parseRule(line, check_restricted=False)
        except ValueError as v:
            logging.error('Parsing:%s:Line:%i', filename, line_no)
            logging.error('Parsing:%s', v.message)
            sys.exit(0)
            
        # Check if we have negated predicates or boolean expressions on the rule. 
        # We haven't studied if that can be done automatically yet.
        if [predicate for predicate in rule[1] if predicate.negated or isinstance(predicate, BooleanExpression)]:
            logging.error('Analyzing:%s:Line:%i', filename, line_no)
            logging.error('Decomposing rules with negated rules or boolean expressions in not supported yet')
            sys.exit(0)
            
        logic_rule = LogicRule(rule[0], rule[1], 0, False, 0, line)
        if (len(logic_rule.body) > 2):
            newRules.extend( decomposeRule(logic_rule) )
        else:
            newRules.append(logic_rule)

    f.close()            
    return newRules

def saveDecomposedRules(logicRules, filename):
    f = open(filename, 'w')
    
    for rule in logicRules:
        head = rule.head
        body = rule.body

        head_str = "{}({})".format(head.id.name,
                                   ", ".join([argument.value for argument in head.arguments]))
        body_str = ", ".join(["{}({})".format(atom.id.name, ", ".join([argument.value for argument in atom.arguments])) 
                              for atom in body])
        f.write(head_str + " :- " + body_str + ".\n")
        
    f.close()
    
if __name__ == '__main__':
    rules = decomposeRulesFromFile('test3.dl')
    print rules
    saveDecomposedRules(rules, 'test-new.dl')
            