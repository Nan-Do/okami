'''
Created on Jan 27, 2014

@author: nando
'''

import sys
import logging

from Parser import parseRule
from Utils import LogicRule

#===============================================================================
# This module is used to decompose a Datalog program right now only the 
# decomposition starting from the left is supported it should suffice for most
# of the cases
#===============================================================================


def getDecomposerRuleMethod(method):
    getDecomposerRuleMethod.decomposed_rules = 0
    
    def generate_new_head(first, second):
        global decomposed_rules
        decomposed_rules += 1
        new_head_name = "Temp_{}".format(str(decomposed_rules))
        new_head_preds = tuple(set(first[1]).symmetric_difference(second[1]))
        return (new_head_name, new_head_preds)
       
    def decomposeRuleLeftMostOuter(logic_rule):
        answers = []
        original_rule = logic_rule.rule
        body = logic_rule.body
        global last_decomposed_rule
        while len(body) > 2:
            # Get the atoms that will be extracted from the current rule to create
            # a new rule
            first, second = body.pop(0), body.pop(0)
            
            # Create the new atom header
            new_head = generate_new_head(first, second)
            
            # Reinsert the new atom
            body.insert(0, new_head)
            
            # Create the new rule
            new_body = (first, second)
            answers.append(LogicRule(new_head, new_body, None, None, original_rule))
            
        answers.insert(0, logic_rule)
        return answers
    
    def decomposeRuleRightMostOuter(logic_rule):
        answers = []
        original_rule = logic_rule.rule
        body = logic_rule.body
        global last_decomposed_rule
        while len(body) > 2:
            # Get the atoms that will be extracted from the current rule to create
            # a new rule
            first, second = body.pop(), body.pop()
            
            # Create the new atom header
            new_head = generate_new_head(first, second)
            
            # Reinsert the new atom
            body.append(new_head)
            
            # Create the new rule
            new_body = (first, second)
            answers.append(LogicRule(new_head, new_body, None, None, original_rule))
            
        answers.insert(0, logic_rule)
        return answers

    buildingRulesAlgorithims = {'leftMostOuter' : decomposeRuleLeftMostOuter,
                                'rigthMostOuter': decomposeRuleRightMostOuter}
    
    if method not in buildingRulesAlgorithims:
        logging.error("{} is an unknown method to decompose the rules".format(method))
        raise ValueError 
    
    return buildingRulesAlgorithims[method]
    
def decomposeRulesFromFile(filename, method='rigthMostOuter'):
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
            newRules.extend(decomposeRule(logic_rule))
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
            