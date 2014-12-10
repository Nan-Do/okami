'''
Created on Jul 12, 2013

@author: nando
'''

from collections import namedtuple

# Identifier is a named tuple. It will be used to identify variables and predicates.
# Name will be a string with a name and unique_id will be a string uniquely among
# all the identifiers.
Identifier = namedtuple('Identifier', ['name', 'unique_id'], verbose=False)

# Argument is a named tuple. Type will hold the type (variable or constant) 
# value will contain the value of the argument. In case of a constant it
# will contain the integer value. Right now constants can only be integers.
Argument = namedtuple('Argument', ['type', 'value'], verbose=False)

# Predicate is a named tuple. Contents
#          id -> It will be the identifier for the predicate.
#     negated -> Boolean that indicates if the predicate is negated in the program.
#   arguments -> A list of arguments.
Predicate = namedtuple('Predicate', ['id', 'negated', 'arguments'], verbose=False)

# Variable is a named tuple. Contents
#         id -> It will be the identifier for the predicate.
#    negated -> Boolean that indicates if the predicate is negated in the program.
Variable = namedtuple('Variable', ['id', 'negated'], verbose=False)

#   LogicRule is a named tuple. Contents:
#     head -> Tuple of two elements the first one is the name, 
#             the second a list of arguments.
#     body -> List of tuples. Every tuple contains two elements,
#             the first one the name of the predicate and the
#             second one the list of arguments.
#     type -> The type of the rules (How many hypothesis it has 1 or 2)
#     lineno -> The line of the rule in the file
#     rule -> string representation of the rule 
LogicRule = namedtuple('LogicRule', ['head', 'body', 'type', 'lineno', 'rule'],
                        verbose=False)

#  RewritingRule1 is a named tuple. Contents:
#     ruleNumber -> The logic rule number associated to the rewriting rule
#     type -> The type of the rules (How many hypothesis it has 1 or 2)
#     leftSideName -> Name of the left side variable
#     leftSideArgs -> List of arguments of the left side of the rewriting rule.
#     rightSideName -> Name of the left side variable
#     rightSideArgs -> List of arguments of the right side of the rewriting rule.
RewritingRule1 = namedtuple('RewritingRule1', ['ruleNumber', 'type', 
                                               'leftVar', 'leftArgs', 
                                               'rightVar', 'rightArgs'],
                            verbose=False)

# May be add a field ViewName to store the viewName every rule is associated to.

#  RewritingRule2 is a named tuple. Contents:
#     ruleNumber -> The logic rule number associated to the rewriting rule
#     type -> The type of the rules (How many hypothesis it has 1 or 2)
#     leftSideName -> Name of the left side variable
#     leftSideArgs -> List of arguments of the left side of the rewriting rule.
#     rightSideName -> Name of the left side variable
#     rightSideArgs -> List of arguments of the right side of the rewriting rule.
#     common_vars -> list of tuples containing the names of the variables and its position inside the rule.
#                    It only stores the variables which are shared, it respects the order inside the rule.
#     consultingPred -> Name of the predicate that will be consulted
#     consultingArgs -> List of arguments containing the values that will be queried on the database
RewritingRule2 = namedtuple('RewritingRule2', ['ruleNumber', 'type',
                                               'leftVar', 'leftArgs', 
                                               'rightVar', 'rightArgs', 
                                               'commonVars', 'consultingPred', 
                                               'consultingArgs', 'aliasName', 
                                               'combinationView'
                                               ],
                            verbose=False)

# PredicateTypes is a named tuple that represents the different kind of 
# predicates that we can find in a datalog program. 
# Contents:
# intensional -> A set with Identifiers for all the intensional predicates
#                of the program. Intensional predicates are those defined by 
#                rules
# extensional -> A set with Identifiers for all the extensional predicates 
#                of the program. Extensional predicates are those not defined 
#                by rules.
PredicateTypes = namedtuple('PredicateTypes', ['intensional', 'extensional'],
                            verbose=False)

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
                                    'predsToViewNames', 'viewsOrdering'],
                       verbose=False)

