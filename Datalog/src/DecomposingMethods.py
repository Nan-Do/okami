'''
Created on Feb 3, 2014

@author: nando
'''

from Types import LogicRule
from itertools import combinations

import re
import random

UNIQUEVAR_TEXT = "#UniqueVar-"
UNIQUEVAR_REGEXP = r"(.+)" + UNIQUEVAR_TEXT + r"(?:\d)+"

decomposed_rules = 0

def generate_new_head(first, second):
    global decomposed_rules
    decomposed_rules += 1
    new_head_name = "Temp_{}".format(str(decomposed_rules))
    new_head_preds = list(set(first[1]).symmetric_difference(second[1]))
    return (new_head_name, new_head_preds)
   
def leftMostDecomposingMethod(logic_rule):
    global last_decomposed_rule
    answers = []
    body = logic_rule.body
    
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
        answers.append(LogicRule(new_head, new_body, None, None, logic_rule.rule))
        
    answers.insert(0, logic_rule)
    return answers

def rightMostDecomposingMethod(logic_rule):
    global last_decomposed_rule
    answers = []
    body = logic_rule.body
    
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
        answers.append(LogicRule(new_head, new_body, None, None, logic_rule.rule))
        
    answers.insert(0, logic_rule)
    return answers

def randomDecomposingMethod(logic_rule):
    global last_decomposed_rule
    answers = []
    body = logic_rule.body
    
    while len(body) > 2:
        # Get the atoms that will be extracted from the body to create
        # a new rule
        first = body.pop(random.randint(0, len(body)-1))
        second = body.pop(random.randint(0, len(body)-1))
        
        # Create the new atom header
        new_head = generate_new_head(first, second)
        
        # Reinsert the new atom
        body.append(new_head)
        
        # Create the new rule
        new_body = (first, second)
        answers.append(LogicRule(new_head, new_body, None, None, logic_rule.rule))
    
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

def generate_logic_rules(rule, rules):
    if isinstance(rule[0][1], list) and isinstance(rule[1][1], list):
        first, second  = rule[0], rule[1]
    elif len(rule[0]) == 2 and isinstance(rule[0][1], tuple):
        first = generate_logic_rules(rule[0], rules)
        second = generate_logic_rules(rule[1], rules)
    else:
        first = rule[0]
        second = generate_logic_rules(rule[1], rules)
        
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
    
def commonVariablesDecomposingMethod(logic_rule):
    global decomposed_rules
    
    # Process the body of the rule to get only the predicate names.
    # We do this to save memory as we have to store all the possible
    # combinations in order to check for duplicates. Also at this point
    # we deal with the problem of duplicated variables names if we
    # we detect a duplicated name we add a long chunk of text and
    # integer (its position in the original rule) to make it unique.
    body_predicates = [] 
    predToVars = {}
    for (position, (name, vars)) in enumerate(logic_rule.body):
        if name in predToVars:
            name = name + UNIQUEVAR_TEXT + str(position)
        body_predicates.append(name)
        predToVars[name] = vars
    
    # Get all the possible unique combinations that can be generated
    # using the given body of the rule. As stated in the formula this
    # number is ((2 * h) - 3))!!. Being h the length of the body. It
    # is equivalent to build all the possible (un)balanced fully rooted
    # binary trees with h children 
    body_combinations = [ body_predicates ]    
    while not all(map((lambda x: len(x)==2), body_combinations)):
        temp_combinations = set()
        for combination in body_combinations:
            for c in combinations(xrange(len(combination)), 2):
                    first, second = combination[c[0]], combination[c[1]]
                    rest = [combination[x] for x in set(xrange(len(combination))).difference(c)]
                    temp_combinations.add(tuple(sorted([(first, second)] + rest)))
        body_combinations = temp_combinations
    
    # At this point we have computed all the possible unique combinations
    # Now we have to obtain the punctuation for every possible combination
    # and keep the best one. The score function maximizes the total number
    # of common variables used while minimizing the length of the generated
    # heads. To do it we reconstruct the rule building again the atoms and
    # compute the punctuation for that combination
    old_value = decomposed_rules
    best_punctuation, best_combination = float("inf"), None 
    for answer in body_combinations:
        rule = reconstruct_rule(answer, predToVars)
        _, punctuation = get_rule_punctuation(rule, 0)
        if punctuation <= best_punctuation:
            best_combination = rule
            best_punctuation = punctuation
    decomposed_rules = old_value
    
    # Once we have the best answer we have to generate all the logical rules
    # that can be derived from the best computed combination
    new_rules = []
    generate_logic_rules(best_combination, new_rules)
    # The previous function generated one more head than needed we have to fix
    # it here and replace the last generated head with the proper rule head
    decomposed_rules -= 1 
    # Modify the last header
    last_rule = new_rules.pop()
    new_rules.append(last_rule._replace(head = logic_rule.head))
    
    return new_rules