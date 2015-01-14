'''
Created on Jul 11, 2013

@author: nando
'''

from Types import RewritingRule1, RewritingRule2
from Types import ViewsData, Argument, Variable

from itertools import chain
from collections import defaultdict

# This function takes care of pretty printing the rewriting equations.
def rewritingEquationPrinter(EquationsTable):
    # This auxiliary function makes an string of the parameter it receives. If
    # it is an integer it means it is a propagated constant trough the rewriting 
    # variable, if it is an argument it means it can be a constant specified on 
    # the program or a variable in which case we just have to call str on it 
    def stringify(x): return 'c_' + str(x) if isinstance(x, int) else str(x.value)
    def parentify(x): return '(' + x + ')'
    
    for eq in EquationsTable:
        # Here we create the string representation of the left side of a rule. It must be formed by
        # constants this constants. This constants can be represented by the variables of the rule in
        # which case are propagated through the rewriting variable or by constants specified on the
        # program itself.
        left_side = []
        for argument, position in eq.leftArgs:
            if argument.type == 'variable':
                left_side.append('c_' + str(position))
            else:
                left_side.append(str(argument.value))
        left_side = ", ".join(left_side)
                
        # Here we are doing the same but for the right side.
        right_side = []
        for element in  eq.rightArgs:
            if isinstance(element, int):
                right_side.append('c_' + str(element))
            else:
                right_side.append(str(element.value))
        right_side = ", ".join(right_side)
        
        # Here we create the rule. 
        rewriting_rule = "x_" + eq.leftVar.id.name + parentify(left_side) +\
            " " + unichr(8658) + "  " +  "x_" + eq.rightVar.id.name + parentify(right_side)
        # If we are dealing with a type 2 rule we have to construct the database query for it.
        if eq.type == 1 and eq.leftVar.negated:
            domain_capital = ', '.join(unichr(120123) + "_" + str(x) for x in xrange(1, len(eq.leftArgs)+1))
            domain_small = ', '.join(unichr(120149) + "_" + str(x) for x in xrange(1, len(eq.leftArgs)+1))
            rewriting_rule += ' ' + unichr(8704) + parentify(domain_capital) + " " + unichr(8713) + \
                                "  " + eq.leftVar.id.name + parentify(domain_small)
        if eq.type == 2:
            consulting_values_str = ', '.join([stringify(x) for x in eq.consultingArgs])
            consulting_variables = [x.value for x in eq.consultingArgs if (isinstance(x, Argument) and x.type == 'variable')]
            consulting_variables_str = ', '.join(consulting_variables)
            
            if consulting_variables:
                rewriting_rule += " " + unichr(8704) + parentify(consulting_variables_str) + " " + unichr(8712) +\
                                  "  " + eq.aliasName + parentify(consulting_values_str)
            else:
                rewriting_rule += " / " + unichr(8708) + " " + eq.aliasName + parentify(consulting_values_str)
        rewriting_rule.encode('utf-8')
                
        print rewriting_rule

# In this function we create a dictionary whose keys will be the arguments
# which represents variables and the values are its positions inside the 
# predicate. This function is used as a base for the reordering algorithms 
def constructVarsMappingFromArgs(arguments):
    # We have to check that we don't update the dictionary with the last appearing
    # position of a variable. As it goes from left to right the first time a 
    # variable appear will fix the index for that variable.  
    r = {}
    for (pos, arg) in enumerate(arguments, start=1):
        if arg.type == 'variable' and arg not in r:
            r[arg] = pos
    return r

     
# This function generates the rewriting rules for logic rules of type 1. It 
# reorders the values to its right position both for the left side of the
# and the right side of the rule. The core it is the constructVarsMappingFromArgs
# function. It also takes care of the constants of the original program.
def generateRuleType_1(rule, rule_number):
    head, body = rule.head, rule.body[0]
    # Create the mapping with the positions of the arguments of the body
    # that are variables if the argument is a constant it won't do anything
    d = constructVarsMappingFromArgs(body.arguments)
    
    # Translate the variables of the head to the right side of the rewriting rule.
    # At the right side we store the argument and the first position of the 
    # argument in case we are dealing with a variable otherwise we store the
    # argument and the position of the argument inside
    right_side_args = []
    for (_, arg) in enumerate(head.arguments, start=1):
        if arg.type == 'variable':
            right_side_args.append(d[arg])
        else:
            right_side_args.append(arg)
    
    # Same as the previous loop but in this case for the body of the logic rule
    # which will become the right side of the rewriting equation.
    left_side_args = []
    for (pos, arg) in enumerate(body.arguments, start=1):
        if arg.type == 'variable':
            left_side_args.append((arg, d[arg]))
        else:
            left_side_args.append((arg, pos))
    
    left_side_var = Variable(body.id, body.negated)
    right_side_var = Variable(head.id, False)
    
    return RewritingRule1(rule_number, 1,
                          left_side_var, left_side_args,
                          right_side_var, right_side_args)

# This function generates the rewriting rules for logic rules of type 2. It 
# reorders the values to its right position both for the left side of the
# and the right side of the rule. It also handles the database part of the
# program as it only affects the rules of type 2.
# It also takes care of the constants of the original program.
def generateRuleType_2a(rule, rule_number):
    head, hyp_1, hyp_2 = rule.head, rule.body[0], rule.body[1]
    # Create the mapping with the positions of the hypothesis of the body
    d = constructVarsMappingFromArgs(hyp_1.arguments)
    
    # Translate the variables of the head to the right side of the rewriting rule.
    # Same as for type 1 rules
    right_side_args = []
    for (_, arg) in enumerate(head.arguments, start=1):
        if arg.type == 'variable' and arg in d:
            right_side_args.append(d[arg])
        else:
            right_side_args.append(arg)

    # This var will contain a list with the variables of the other hypothesis, 
    # the variables will be a Variable or an integer representing a position in the list
    # of common variables
    other_hypothesis = []
    # Common_vars will contain a list of the common variables. As the list should not contain
    # duplicates we use a temp set to avoid adding duplicates them.
    common_args = []
    temp_common_args = set()
    for (pos, arg) in enumerate(hyp_2.arguments, start=1):
        if arg in  d:
            other_hypothesis.append(d[arg])
            element = (arg, d[arg]) 
            if (element not in temp_common_args):
                common_args.append(element)
                temp_common_args.add(element)
        else: 
            other_hypothesis.append(arg)
            
    # When we add the left constants of the rewriting rule we have to check if
    # it is a repeated variable in that case use the first position in which
    # appears 
    left_side_args = []
    for (pos, arg) in enumerate(hyp_1.arguments, start=1):
        if arg.type == 'variable':
            left_side_args.append((arg, d[arg]))
        else:
            left_side_args.append((arg, pos))
        
        
    # Get the view name
    view = []
    order, combination = constructOrderingForView(other_hypothesis)
    for element in order:
        if isinstance(element, int):
            view.append(hyp_2.arguments[other_hypothesis.index(element)])
        else:
            view.append(element)
    
    view_name = hyp_2.id.name + '_' + ''.join([str(x.value) for x in view]).lower()
    
    left_side_var = Variable(hyp_1.id, hyp_1.negated)
    right_side_var = Variable(head.id, False)
    consulting_pred_var = Variable(hyp_2.id, hyp_2.negated)
    
    return RewritingRule2(rule_number, 2, 
                          left_side_var, left_side_args, 
                          right_side_var, right_side_args, 
                          common_args, consulting_pred_var,
                          order, view_name, combination)

# This function is analogous to the previous one but it takes care of the
# other hypothesis of the rules of type 2.  
def generateRuleType_2b(rule, rule_number):
    head, hyp_1, hyp_2 = rule.head, rule.body[0], rule.body[1] 
    d = constructVarsMappingFromArgs(hyp_2.arguments)
    
    right_side_args = []
    for (_, arg) in enumerate(head.arguments, start=1):
        if arg.type == 'variable' and arg in d:
            right_side_args.append(d[arg])
        else:
            right_side_args.append(arg)
            
    other_hypothesis = []
    # As the list should not contain duplicates we use a set to avoid adding duplicates 
    # to the list.
    common_args = []
    temp_common_args = set()
    for (pos, arg) in enumerate(hyp_1.arguments, start=1):
        if arg in  d:
            other_hypothesis.append(d[arg])
            element = (arg, d[arg]) 
            if (element not in temp_common_args):
                common_args.append(element)
                temp_common_args.add(element)
        else: 
            other_hypothesis.append(arg)
            
    left_side_args = []
    for (pos, arg) in enumerate(hyp_2.arguments, start=1):
        if arg.type == 'variable':
            left_side_args.append((arg, d[arg]))
        else:
            left_side_args.append((arg, pos))
            
        
    # Get the view name
    view = []
    order, combination = constructOrderingForView(other_hypothesis)
    for element in order:
        if isinstance(element, int):
            view.append(hyp_1.arguments[other_hypothesis.index(element)])
        else:
            view.append(element)
            
    view_name = hyp_1.id.name + '_' + ''.join([str(x.value) for x in view]).lower()
    
    left_side_var = Variable(hyp_2.id, hyp_2.negated)
    right_side_var = Variable(head.id, False)
    consulting_pred_var = Variable(hyp_1.id, hyp_1.negated)
    
    return RewritingRule2(rule_number, 2, 
                          left_side_var, left_side_args, 
                          right_side_var, right_side_args, 
                          common_args, consulting_pred_var,
                          order, view_name, combination)  
        
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

# This function provides the ordering for the view. The new ordering put the
# integers (shared variables) and constant arguments at the beginning of the 
# new ordering. It also keeps tracking of the changes made on the combination. 
# This set of changes will be the identifier for the view. The function returns
# the new ordering which is the list of consultingArgs reordered and the
# combination which is the list.
def constructOrderingForView(consultingArgs):
    new_order = consultingArgs[:]
    combination = list(xrange(1, len(new_order)+1))
    count = 0
    
    # First we put the integers on the list. These ints represents the
    # shared variables on the original datalog program.
    for i in xrange(len(new_order)):
        if isinstance(new_order[i], int):
            count += 1
        else:
            break
        
    for i in xrange(count, len(new_order)):
        if isinstance(new_order[i], int):
            new_order.insert(count, new_order.pop(i))
            combination.insert(count, combination.pop(i))
            count += 1
            
    # Then we put the arguments that are constants. These represents the
    # constants on the original datalog program.
    for i in xrange(count, len(new_order)):
        if isinstance(new_order[i], Argument) and\
          new_order[i].type == "constant":
            count += 1
        else:
            break
            
    for i in xrange(count, len(new_order)):
        if isinstance(new_order[i], Argument) and\
          new_order[i].type == "constant":
            new_order.insert(count, new_order.pop(i))
            combination.insert(count, combination.pop(i))
            count += 1
           
    return new_order, combination
            
def rewritingEquationGenerator(rulesTable, printEquations=False):
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
                
                # If the rewriting rule has the left variable negated we have to continue.
                # Negated predicates are only used to be queried, practically this restrict 
                # the set of valid solutions. The database is populated as an extensional 
                # database or in a previous stratum 
                if rewriting_rule.leftVar.negated:
                    continue
                
                if (not check_consulting_values(rewriting_rule.consultingArgs)):
                    print "Warning with rule: " + logic_rule.rule + " Consulting predicate " +\
                        rewriting_rule.consultingPred + " has to create another view " +\
                        rewriting_rule.aliasName
                
                consultingPred_id = rewriting_rule.consultingPred.id
                combinationView = rewriting_rule.combinationView
                aliasName = rewriting_rule.aliasName  
                
                c = predicate_to_ViewData[consultingPred_id]
                viewName = next((x[0] for x in c if combinationView == x[1]), None)
                if viewName == None:
                    if len(c) == 0:
                        viewName = consultingPred_id.name + '_view_1'
                    else:
                        viewName = consultingPred_id.name + '_view_' + str(int(c[-1][0][-1]) + 1)
                        
                    predicate_to_ViewData[consultingPred_id].append((viewName, combinationView))
                
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
