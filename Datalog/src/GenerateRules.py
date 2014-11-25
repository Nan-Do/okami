'''
Created on Jul 11, 2013

@author: nando
'''

from Types import RewritingRule1, RewritingRule2, ViewsData
from itertools import chain
from collections import defaultdict

def printRewritingEquations(EquationsTable):
    def stringify(x): return x if isinstance(x, str) else 'c_' + str(x)
    def parentify(x): return '(' + x + ')'
    
    for eq in EquationsTable:
        # To build the left side we have to check if we are dealing with a variable and its position
        # or with a constant if it is a variable we switch by its position and if it is a constant
        # we just plug it.
        left_side = []
        for argument, position in  eq.leftSideCons:
            if argument.type == 'variable':
                left_side.append('c_' + str(position))
            else:
                left_side.append(str(argument.value))
        left_side = ", ".join(left_side)
                
        # Here we are doing the same but for the right side.
        right_side = []
        for argument, position in  eq.rightSideCons:
            if argument.type == 'variable':
                right_side.append('c_' + str(position))
            else:
                right_side.append(str(argument.value))
        right_side = ", ".join(right_side)
        
        rewriting_rule = "x_" + eq.leftSideName + parentify(left_side) +\
            " => " +  "x_" + eq.rightSideName + parentify(right_side)
        if eq.type == 2:
            consulting_values = ', '.join([stringify(x) for x in eq.consultingValues])
            consulting_variables = ', '.join([x for x in eq.consultingValues if isinstance(x, str)])
            
            rewriting_rule += " " + unichr(8704) + parentify(consulting_variables) + " " + unichr(8712) +\
                " " + eq.aliasName + parentify(consulting_values)
            rewriting_rule.encode('utf-8')
                
        print rewriting_rule

def buildDictWithVars(arguments):
    # We have to check that we don't update the dict with the last appearing
    # position of a variable. As it goes from left to right the first time a 
    # var appear will fix the index for that variable  
    r = {}
    for (pos, arg) in enumerate(arguments, start=1):
        if arg.type == 'variable' and arg not in r:
            r[arg] = pos
    return r

    # One liners that doesn't work properly
    #return {var: 'c_' + str(pos+1) for (pos, var) in enumerate(variables)}
    #return {var: pos+1 for (pos, var) in enumerate(variables)}
        
# This function generates rewriting rules for logic rules of type 1 it just 
# creates a dictionary whose keys are the variables of the body, which will
# be the left side of the rewriting rule, and its position as a value then
# it just translates the variables into the correct ordering.
def generateRuleType_1(rule, rule_number):
    head, body = rule.head, rule.body[0]
    # Create the mapping with the positions of the arguments of the body
    # that are variables if the argument is a constant it won't do anything
    d = buildDictWithVars(body[1])
    
    left_side = []
    right_side = []

    # Translate the variables of the head to the right side of the rewriting rule.
    # At the right side we store the argument and the first position of the 
    # argument in case we are dealing with a variable otherwise we store the
    # argument and the position of the argument inside
    for (pos, arg) in enumerate(head[1], start=1):
        if arg.type == 'variable':
            right_side.append((arg, d[arg]))
        else:
            right_side.append((arg, pos))
    
    # Same as the previous loop but in this case for the body of the logic rule
    # which will become the right side of the rewriting equation.
    for (pos, arg) in enumerate(body[1], start=1):
        if arg.type == 'variable':
            left_side.append((arg, d[arg]))
        else:
            left_side.append((arg, pos))
    
    return RewritingRule1(rule_number, 1, body[0], 
                          left_side, head[0], 
                          right_side)
    
def generateRuleType_2a(rule, rule_number):
    head, hyp1, hyp2 = rule.head, rule.body[0], rule.body[1]
    # Create the mapping with the positions of the hypothesis of the body
    d = buildDictWithVars(hyp1[1])
    
    # Translate the variables of the head to the right side of the rewriting rule.
    # Same as for type 1 rules
    right_side = []
    for (pos, arg) in enumerate(head[1], start=1):
        if arg.type == 'variable' and arg in d:
            right_side.append((arg, d[arg]))
        else:
            right_side.append((arg, pos))

    # This var will contain a list with the variables of the other hypthesis, 
    # the variables will be a Variable or an integer representing a position in the list
    # of common variables
    other_hypothesis = []
    # Common_vars will contain a list of the common vars. As the list should not contain
    # duplicates we use a temp set to avoid adding duplicates them.
    common_vars = []
    temp_common_vars = set()
    for (pos, arg) in enumerate(hyp2[1], start=1):
        if arg in  d:
            other_hypothesis.append(d[arg])
            element = (arg, d[arg]) 
            if (element not in temp_common_vars):
                common_vars.append(element)
                temp_common_vars.add(element)
        else: 
            other_hypothesis.append(arg)
            
    # When we add the left constants of the rewriting rule we have to check if
    # it is a repeated variable in that case use the first position in which
    # appears 
    left_side = []
    for (pos, arg) in enumerate(hyp1[1], start=1):
        if arg.type == 'variable':
            left_side.append((arg, d[arg]))
        else:
            left_side.append((arg, pos))
        
        
    # Get the view name
    view = []
    order, combination = give_correct_order_for_view(other_hypothesis)
    for element in order:
        if isinstance(element, int):
            view.append(hyp2[1][other_hypothesis.index(element)])
        else:
            view.append(element)
    
    view_name = hyp2[0] + '_' + ''.join([str(x.value) for x in view]).lower()
    
    return RewritingRule2(rule_number, 2, hyp1[0], left_side, head[0], 
                          right_side, common_vars, hyp2[0], order, 
                          view_name, combination)
    
def generateRuleType_2b(rule, rule_number):
    head, hyp1, hyp2 = rule.head, rule.body[0], rule.body[1] 
    d = buildDictWithVars(hyp2[1])
    
    right_side = []
    for (pos, arg) in enumerate(head[1], start=1):
        if arg.type == 'variable' and arg in d:
            right_side.append((arg, d[arg]))
        else:
            right_side.append((arg, pos))
            
    other_hypothesis = []
    # As the list should not contain duplicates we use a set to avoid adding duplicates 
    # to the list.
    common_vars = []
    temp_common_vars = set()
    for pos, var in enumerate(hyp1[1], start=1):
        if var in  d:
            other_hypothesis.append(d[var])
            element = (var, d[var]) 
            if (element not in temp_common_vars):
                common_vars.append(element)
                temp_common_vars.add(element)
        else: 
            other_hypothesis.append(var)
            
    # When we add the left constants of the rewriting rule we have to check if
    # it is a repeated variable in that case use the first position in which
    # appears 
    left_constants = []
    #for pos, var in enumerate(hyp2[1], start=0):
    #    if var not in hyp2[1][:pos]:
    #        left_constants.append((var,pos+1))
    #    else:
    #        left_constants.append((var,hyp2[1].index(var)+1))
    left_side = []
    for (pos, arg) in enumerate(hyp2[1], start=1):
        if arg.type == 'variable':
            left_side.append((arg, d[arg]))
        else:
            left_side.append((arg, pos))
            
        
    # Get the view name
    view = []
    order, combination = give_correct_order_for_view(other_hypothesis)
    for element in order:
        if isinstance(element, int):
            view.append(hyp1[1][other_hypothesis.index(element)])
        else:
            view.append(element)
            
    view_name = hyp1[0] + '_' + ''.join([str(x.value) for x in view]).lower()
    
    return RewritingRule2(rule_number, 2, hyp2[0], left_constants, head[0],
                          right_side, common_vars, hyp1[0], order, 
                          view_name, combination)  
        
def analyzeRule(rule):
    head, body = rule.head, rule.body
    
    if rule.type == 1:
        if set(head[1]) != set(body[0][1]) or len(head[1]) != len(body[0][1]):
            print "Unbound variable in line:", rule.lineno, ":", rule.rule
            raise ValueError

def check_consulting_values(consulting_values):
    check_only_string_vars = False
    
    for element in consulting_values:
        if check_only_string_vars and isinstance(element, int):
            return False 
        
        if isinstance(element, str):
            check_only_string_vars = True 
    
    return True

# This function gives an order for the views it keeps track of the integers,
# the integer represent the position of the shared variables. The new ordering
# put the integers at the beginning in the new ordering while keeping track of the
# changes on the combination which will be the combination that identifies the view. 
def give_correct_order_for_view(consultingValues):
    new_order = []
    combination = list(xrange(1, len(consultingValues)+1))
    count = 0
    
    for i in xrange(len(consultingValues)):
        if isinstance(consultingValues[i], int):
            new_order.append(consultingValues[i])
            count += 1
        else:
            break
        
    for i in xrange(count, len(consultingValues)):
        if isinstance(consultingValues[i], int):
            new_order.insert(count, consultingValues[i])
            combination.insert(count, combination.pop(i))
            count += 1
        else:
            new_order.append(consultingValues[i])
            
    return new_order, combination
            
def generateRules(rulesTable, printEquations=False):
    equationsTable = []
    predicate_to_ViewData = defaultdict(list)
    alias_to_ViewNames = {}
    
    for rule_number, logic_rule in enumerate(rulesTable, start=1):
        
        #analyzeRule(logic_rule)
        if logic_rule.type == 1:
            equationsTable.append(generateRuleType_1(logic_rule, rule_number))

        if logic_rule.type == 2:
            for rewriting_rule in [generateRuleType_2a(logic_rule, rule_number),
                              generateRuleType_2b(logic_rule, rule_number)]:
                
                if (not check_consulting_values(rewriting_rule.consultingValues)):
                    print "Warning with rule: " + logic_rule.rule + " Consulting predicate " +\
                        rewriting_rule.consultingPred + " has to create another view " +\
                        rewriting_rule.aliasName
                
                consultingPred = rewriting_rule.consultingPred
                combinationView = rewriting_rule.combinationView
                aliasName = rewriting_rule.aliasName  
                
                c = predicate_to_ViewData[consultingPred]
                viewName = next((x[0] for x in c if combinationView == x[1]), None)
                if viewName == None:
                    if len(c) == 0:
                        viewName = consultingPred + '_view_1'
                    else:
                        viewName = consultingPred + '_view_' + str(int(c[-1][0][-1]) + 1)
                        
                    predicate_to_ViewData[consultingPred].append((viewName, combinationView))
                
                # TODO: Check that this always works, also make it more sophisticated
                # to detect rules that are semantically equal. 
                if aliasName not in alias_to_ViewNames:
                    alias_to_ViewNames[aliasName] = viewName
                elif alias_to_ViewNames[aliasName] != viewName:
                    new_alias = aliasName + '_' + str(rewriting_rule.ruleNumber)
                    alias_to_ViewNames[new_alias] = viewName
                    rewriting_rule = rewriting_rule._replace(aliasName=new_alias)
                    
                equationsTable.append(rewriting_rule)
                
                
    # Fill the data
    preds_to_viewNames = defaultdict(list)
    for predicate, list_of_views in predicate_to_ViewData.iteritems():
        for view in list_of_views:
            preds_to_viewNames[predicate].append(view[0])

    viewNames_to_combinations = dict(chain(*predicate_to_ViewData.itervalues()))
    
    # Establish the order of the views in the data structure
    # The order is based in the length of the predicates. The longest
    # predicates go first. In that way we can mix the different data 
    # structures into just one 
    viewsOrdering = tuple((x[0], pos) for pos, x in enumerate(sorted(viewNames_to_combinations.iteritems(),
                                                                     key=lambda x: len(x[1]),
                                                                     reverse=True)) )
    
    viewsData = ViewsData(viewNames_to_combinations, alias_to_ViewNames,
                          preds_to_viewNames, viewsOrdering)
    
    return equationsTable, viewsData 


if __name__ == '__main__':
    pass
