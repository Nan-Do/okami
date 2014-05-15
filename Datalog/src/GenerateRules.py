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
        left_constants = ", ".join(['c_' + str(x[1]) for x in eq.leftSideCons])
        right_constants = ", ".join([stringify(x) for x in eq.rightSideCons])
        rewriting_rule = "x_" + eq.leftSideName + parentify(left_constants) +\
            " => " +  "x_" + eq.rightSideName + parentify(right_constants)
        if eq.type == 2:
            consulting_values = ', '.join([stringify(x) for x in eq.consultingValues])
            consulting_variables = ', '.join([x for x in eq.consultingValues if isinstance(x, str)])
            
            rewriting_rule += " " + unichr(8704) + parentify(consulting_variables) + " " + unichr(8712) +\
                " " + eq.aliasName + parentify(consulting_values)
            rewriting_rule.encode('utf-8')
                
        print rewriting_rule

def buildDictWithVars(variables):
    # We have to check that we don't update the dict with the last appearing
    # position of a variable. As it goes from left to right the first time a 
    # var appear will fix the index for that variable  
    r = {}
    for (pos, var) in enumerate(variables):
        if var not in r:
            r[var] = pos+1
    return r

    # One liners that doesn't work properly
    #return {var: 'c_' + str(pos+1) for (pos, var) in enumerate(variables)}
    #return {var: pos+1 for (pos, var) in enumerate(variables)}
        
def generateRuleType_1(rule, rule_number):
    head, body = rule.head, rule.body[0]
    d = buildDictWithVars(body[1])
    
    used_vars = {}    
    left_constants = []
    right_constants = []

    for var in head[1]:
        right_constants.append(d[var])
    
    for pos, var in enumerate(body[1], start=1):
        if var in used_vars:
            left_constants.append((var, used_vars[var]))
        else:
            used_vars[var] = pos 
            left_constants.append((var, pos))
        
    return RewritingRule1(rule_number, 1, body[0], 
                          left_constants, head[0], 
                          right_constants)
    
def generateRuleType_2a(rule, rule_number):
    head, hyp1, hyp2 = rule.head, rule.body[0], rule.body[1] 
    d = buildDictWithVars(hyp1[1])
    
    right_constants = []
    for pos,var in enumerate(head[1]):
        if var in d:
            right_constants.append(d[var])
        else:
            right_constants.append(var)
            
    other_hyp_cons = []
    # As the list should not contain duplicates we use a set to avoid adding duplicates 
    # to the list.
    common_vars = []
    temp_common_vars = set()
    for pos, var in enumerate(hyp2[1], start=1):
        if var in  d:
            other_hyp_cons.append(d[var])
            element = (var, d[var]) 
            if (element not in temp_common_vars):
                common_vars.append(element)
                temp_common_vars.add(element)
        else: 
            other_hyp_cons.append(var)
            
    # When we add the left constants of the rewriting rule we have to check if
    # it is a repeated variable in that case use the first position in which
    # appears 
    left_constants = []
    for pos, var in enumerate(hyp1[1], start=0):
        if var not in hyp1[1][:pos]:
            left_constants.append((var,pos+1))
        else:
            left_constants.append((var,hyp1[1].index(var)+1))
        
    # Get the view name
    view = []
    order, combination = give_correct_order_for_view(other_hyp_cons)
    for element in order:
        if isinstance(element, int):
            view.append(hyp2[1][other_hyp_cons.index(element)])
        else:
            view.append(element)
     
    view_name = hyp2[0] + '_' + ''.join(view).lower()
    
    return RewritingRule2(rule_number, 2, hyp1[0], left_constants, head[0], 
                          right_constants, common_vars, hyp2[0], order, 
                          view_name, combination)
    
def generateRuleType_2b(rule, rule_number):
    head, hyp1, hyp2 = rule.head, rule.body[0], rule.body[1] 
    d = buildDictWithVars(hyp2[1])
    
    right_constants = []
    for pos,var in enumerate(head[1]):
        if var in d:
            right_constants.append(d[var])
        else:
            right_constants.append(var)
            
    other_hyp_cons = []
    # As the list should not contain duplicates we use a set to avoid adding duplicates 
    # to the list.
    common_vars = []
    temp_common_vars = set()
    for pos, var in enumerate(hyp1[1], start=1):
        if var in  d:
            other_hyp_cons.append(d[var])
            element = (var, d[var]) 
            if (element not in temp_common_vars):
                common_vars.append(element)
                temp_common_vars.add(element)
        else: 
            other_hyp_cons.append(var)
            
    # When we add the left constants of the rewriting rule we have to check if
    # it is a repeated variable in that case use the first position in which
    # appears 
    left_constants = []
    for pos, var in enumerate(hyp2[1], start=0):
        if var not in hyp2[1][:pos]:
            left_constants.append((var,pos+1))
        else:
            left_constants.append((var,hyp2[1].index(var)+1))
            
        
    # Get the view name
    view = []
    order, combination = give_correct_order_for_view(other_hyp_cons)
    for element in order:
        if isinstance(element, int):
            view.append(hyp1[1][other_hyp_cons.index(element)])
        else:
            view.append(element)
            
    view_name = hyp1[0] + '_' + ''.join(view).lower()
    
    return RewritingRule2(rule_number, 2, hyp2[0], left_constants, head[0],
                          right_constants, common_vars, hyp1[0], order, 
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
