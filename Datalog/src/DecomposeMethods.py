'''
Created on Feb 3, 2014

@author: nando
'''

from Utils import LogicRule


decomposed_rules = 0
    
def generate_new_head(first, second):
    global decomposed_rules
    decomposed_rules += 1
    new_head_name = "Temp_{}".format(str(decomposed_rules))
    new_head_preds = tuple(set(first[1]).symmetric_difference(second[1]))
    return (new_head_name, new_head_preds)
   
def ruleLeftMostOuterDecomposeMethod(logic_rule):
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

def ruleRightMostOuterDecomposeMethod(logic_rule):
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