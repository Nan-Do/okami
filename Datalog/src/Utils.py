'''
Created on Jul 12, 2013

@author: nando
'''

from collections import namedtuple

#   LogicRule is a named tuple. Contents:
#     head -> Tuple of two elements the first one is the name, 
#             the second a list with the variables
#     body -> List of tuples. Every tuple contains two elements,
#             the first one the name of the predicate and the
#             second one the list of variables
#     type -> The type of the rules (How many hypothesis it has 1 or 2)
#     lineno -> The line of the rule in the file
#     rule -> string representation of the rule 
LogicRule = namedtuple('LogicRule', ['head', 'body', 'type', 'lineno', 'rule'],
                        verbose=False)

#  RewritingRule1 is a named tuple. Contents:
#     ruleNumber -> The logic rule number associated to the rewriting rule
#     type -> The type of the rules (How many hypothesis it has 1 or 2)
#     leftSideName -> Name of the left side variable
#     leftSideCons -> List of constants of the left side. List of integers
#     rightSideName -> Name of the left side variable
#     rightSideCons -> List of constants of the left side. List of integers
RewritingRule1 = namedtuple('RewritingRule1', ['ruleNumber', 'type', 
                                               'leftSideName', 'leftSideCons', 
                                               'rightSideName', 'rightSideCons'])

# May be add a field ViewName to store the viewName every rule is associated to.

#  RewritingRule2 is a named tuple. Contents:
#     ruleNumber -> The logic rule number associated to the rewriting rule
#     type -> The type of the rules (How many hypothesis it has 1 or 2)
#     leftSideName -> Name of the left side variable
#     leftSideCons -> List of constants of the left side. List of integers
#     rightSideName -> Name of the left side variable
#     rightSideCons -> List of constants of the left side. List of integers and variable names
#     common_vars -> set containing the names of the variables which are shared
#     consultingPred -> Name of the predicate that will be consulted
#     consultingValues -> List of the variables that 
RewritingRule2 = namedtuple('RewritingRule2', ['ruleNumber', 'type',
                                               'leftSideName', 'leftSideCons', 
                                               'rightSideName', 'rightSideCons', 
                                               'common_vars', 'consultingPred', 
                                               'consultingValues', 'aliasName', 
                                               'combinationView'
                                               ])

# PredicateTypes is a named tuple that represents the different kind of 
# predicates that we can find in a datalog program. 
# Contents:
# intensional -> A set with strings identifying all the intensional predicates
#                of the program. Intensional predicates are those defined by 
#                rules
# extensional -> A set with strings identifying all the extensional predicates 
#                of the program. Extensional predicates are those not defined 
#                by rules.
PredicateTypes = namedtuple('PredicateTypes', ['intensional', 'extensional'])

# ViewsData is a named tuple that represents the information we need to
# handle the different views our datalog program need
# Contents:
# viewNamesToCombinations -> Dictionary containing the view names represented   
#                            as (pred_name)_view_number, basically is a string
#                            representation for every combination, as key. And 
#                            the Combination represented as a list of integers 
#                            as value
# aliasToViewNames -> Dictionary containing the alias given to every view as 
#                     keys. An alias is (pred_name)_(variables_of_the_predicate).
#                     And the view names as explained before as values
# predsToViewNames -> Default dictionary containing the predicate names as keys and
#                     a list of the name views it is related as values
# viewsOrdering    -> Is an ordered tuple that contains the name view as a first
#                     element of every tuple, and the given order as the second.
#                     This ordering is based on the length of the combinations
#                     the longest combinations go first. This is required in 
#                     order to have only one data structure in C.
ViewsData = namedtuple('ViewsData',['viewNamesToCombinations', 'aliasToViewNames',
                                    'predsToViewNames', 'viewsOrdering'])

