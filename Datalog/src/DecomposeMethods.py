'''
Created on Feb 3, 2014

@author: nando
'''

from Utils import LogicRule
from itertools import combinations
import re

UNIQUEVAR_REGEXP = r"(.+)#UniqueVar-(?:\d)+"

decomposed_rules = 0

def generate_new_head(first, second):
    global decomposed_rules
    decomposed_rules += 1
    new_head_name = "Temp_{}".format(str(decomposed_rules))
    new_head_preds = list(set(first[1]).symmetric_difference(second[1]))
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


def get_punctuation(first, second):
    return len(set(first[1]).intersection(second[1]))

def get_rule_punctuation(rule, punctuation):
    if isinstance(rule[0][1], list) and isinstance(rule[1][1], list):
        first, second  = rule[0], rule[1]
    elif len(rule[0]) == 2 and isinstance(rule[0][1], tuple):
        first, temp_punct = get_rule_punctuation(rule[0], punctuation)
        second, punctuation = get_rule_punctuation(rule[1], punctuation + temp_punct)
    else:
        first = rule[0]
        second, punctuation = get_rule_punctuation(rule[1], punctuation)
    
    head = generate_new_head(first, second)
    #new_punctuation = get_punctuation(first, second)
    new_punctuation = len(head[1])
    
    return head, punctuation + new_punctuation

def generate_new_rules(rule, rules):
    if isinstance(rule[0][1], list) and isinstance(rule[1][1], list):
        first, second  = rule[0], rule[1]
    elif len(rule[0]) == 2 and isinstance(rule[0][1], tuple):
        first = generate_new_rules(rule[0], rules)
        second = generate_new_rules(rule[1], rules)
    else:
        first = rule[0]
        second = generate_new_rules(rule[1], rules)
        
    head = generate_new_head(first, second)
    #rules.append( (head, [(first, second)] ) )
    match = re.match(UNIQUEVAR_REGEXP, first[0])
    if match:
        first = ( match.group(1), first[1] )
    match = re.match(UNIQUEVAR_REGEXP, second[0])
    if match:
        second = ( match.group(1), second[1] )
    
    rules.append( LogicRule(head, [first, second], None, None, "")) 
    
    
    return head

def reconstruct_rule(answer, predToVars):
    if isinstance(answer[0], str) and isinstance(answer[1], str):
        first = (answer[0], predToVars[answer[0]])
        second = (answer[1], predToVars[answer[1]])
    elif len(answer[0]) == 2 and isinstance(answer[0], tuple):
        first = reconstruct_rule((answer[0][0], answer[0][1]), predToVars)
        second = reconstruct_rule(answer[1], predToVars)
    else:
        first = (answer[0], predToVars[answer[0]])
        second = reconstruct_rule(answer[1], predToVars)
        
    return (first, second)
    
def mostCommonVariablesDecomposeMethod(logic_rule):
    global decomposed_rules
    # Get the name of the body predicates
    #answers = [ [ predicate[0] for predicate in logic_rule.body ] ]
    #predToVars = dict(logic_rule.body)
    answers = [] 
    predToVars = {}
    for (p, (name, vars)) in enumerate(logic_rule.body):
        if name in predToVars:
            name = name + "#UniqueVar-" + str(p)
        answers.append(name)
        predToVars[name] = vars
    
    answers = [ answers ]
    print answers
    print predToVars                  
            
    # Get all the posible combinations
    while not all(map((lambda x: len(x)==2), answers)):
        new_answers = set()
        for answer in answers:
            for c in combinations(xrange(len(answer)), 2):
                    first, second = answer[c[0]], answer[c[1]]
                    rest = [answer[x] for x in set(xrange(len(answer))).difference(c)]
                    new_answers.add(tuple(sorted([(first, second)] + rest)))
        answers = new_answers
    # At this point we have all the possible combinations computed
    # Now obtain the punctuation and choose the best one
    old_value = decomposed_rules
    best_punctuation, best_answer = float("inf"), None 
    for answer in answers:
        rule = reconstruct_rule(answer, predToVars)
        _, punctuation = get_rule_punctuation(rule, 0)
        if punctuation <= best_punctuation:
            best_answer = rule
            best_punctuation = punctuation
    decomposed_rules = old_value
    new_rules = []
    print best_answer
    generate_new_rules(best_answer, new_rules)
    decomposed_rules -= 1 
    # Modify the last header
    last_rule = new_rules.pop()
    new_rules.append(last_rule._replace(head = logic_rule.head))
    return new_rules