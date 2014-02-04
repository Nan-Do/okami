'''
Created on Jan 27, 2014

@author: nando
'''

import sys
import logging

from Parser import parseRule
from Utils import LogicRule
from DecomposeMethods import ruleRightMostOuterDecomposeMethod, ruleLeftMostOuterDecomposeMethod,\
    mostCommonVariablesDecomposeMethod

#===============================================================================
# This module is used to decompose a Datalog program right now only the 
# decomposition starting from the left is supported it should suffice for most
# of the cases
#===============================================================================


def getDecomposerRuleMethod(method):
    buildingRulesAlgorithims = {'leftMostOuter' : ruleLeftMostOuterDecomposeMethod,
                                'rigthMostOuter': ruleRightMostOuterDecomposeMethod,
                                'mostCommonVariables': mostCommonVariablesDecomposeMethod}
    
    if method not in buildingRulesAlgorithims:
        logging.error("{} is an unknown method to decompose the rules".format(method))
        raise ValueError 
    
    return buildingRulesAlgorithims[method]
    
def decomposeRulesFromFile(filename, method='mostCommonVariables'):
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
            
        logic_rule = LogicRule(rule[0], rule[1], None, None, line)
        if (len(logic_rule.body) > 2):
            newRules.extend( decomposeRule(logic_rule) )
        else:
            newRules.append(logic_rule)

    f.close()            
    return newRules

def saveDecomposedRules(logicRules, filename):
    f = open(filename, 'w')
    
    for rule in logicRules:
        head_str = "{}({})".format(rule.head[0], ", ".join(rule.head[1]))
        body_str = ", ".join(["{}({})".format(atom[0], ", ".join(atom[1])) for atom in rule.body])
        f.write(head_str + " :- " + body_str + ".\n")
        
    f.close()
    
if __name__ == '__main__':
    rules = decomposeRulesFromFile('test.dl')
    print rules
    saveDecomposedRules(rules, 'test-new.dl')
            