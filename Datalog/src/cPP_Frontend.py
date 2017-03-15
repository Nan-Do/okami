'''
Created on Jan 30, 2017

@author: nando
'''

import os
import shutil
import sys

from collections import namedtuple, defaultdict, Counter
from operator import attrgetter
from functools import wraps
from itertools import count, chain, repeat
from datetime import datetime

from Types import Argument, ArithmeticExpression
from django.template.defaultfilters import length


# Settings for the parser
DELIMITER = '%%'
SOURCE_DIRECTORY = "CPP_Template"
#OUTPUT_DIRECTORY = "./"

INCLUDE_FILES = ['rewritingvariable.hh', 'variabletype.hh', 'views.hh', 'lockedvectorint.hh',
                 'lockedbitset.hh', 'datastructure.hh', 'solver.hh']

SOURCE_FILES = ['main.cc', 'datastructure.cc', 'solver.cc', 'makefile']

EMPTY_LINE = '\n'
SPACES = ' ' * 4

DEBUG = False

# Global data for the module
GenerationData = None

def getExtensionalPredicates():
    return chain(*map(attrgetter('block1'), map(attrgetter('ordering'), GenerationData.stratums)))

# This function returns an itertaror to all the views contained in the stratums
def getViewsFromAllStratums():
    return map(attrgetter('views'), GenerationData.stratums)

def getEquationsFromAllStratums():
    return chain(*map(attrgetter('equations'), GenerationData.stratums))

def getAllPredicatesIDs():
    return set(chain.from_iterable(map(list,
                                       map(lambda x: chain(x.ordering.block1,
                                                           x.ordering.block2,
                                                           x.ordering.block3),
                                           GenerationData.stratums))))

def getPredicateLength(predicate):
    for eq in getEquationsFromAllStratums():
        if predicate == eq.leftVariable.id:
            return len(eq.leftArguments)
        elif predicate == eq.rightVariable.id:
            return len(eq.rightArguments)
        else:
            for negated_elment in eq.negatedElements:
                if predicate == negated_elment.id:
                    return len(negated_elment.arguments)
            
    #print "None"
    return None

def getQueryMinimumLength():
    #return min(len(x.leftArguments) for x in GenerationData.equationsTable if x.type == 2)
    return min(len(x.leftArguments) for x in getEquationsFromAllStratums() if x.type == 2)

def getQueryMaximumLength():
    #return max(len(x.leftArguments) for x in GenerationData.equationsTable if x.type == 2)
    return max(len(x.leftArguments) for x in getEquationsFromAllStratums() if x.type == 2)

# Decorators
def check_for_predicates_of_type2(view_func):
    def _decorator(request, *args, **kwargs):
        response = None
        # Make sure we don't call the function if we don't have predicates of type 2
        if len([x for x in getEquationsFromAllStratums() if x.type == 2]):
            response = view_func(request, *args, **kwargs)
        return response
    return wraps(view_func)(_decorator)

# In order to get the minimum node and the maximum node we have to check the right side
# of every rule to store the answers and the left side of the rule of type 2
def getDataStructureNodesMaximumLength():
    return  max(chain([len(x.leftArguments) for x in getEquationsFromAllStratums() if x.type == 2],
                      [len(x.rightArguments) for x in getEquationsFromAllStratums()]))

# This function checks to see if there are predicates that appearing in some
# rule being all its variables equal cards. 
# The function returns a set of strings, every string represents the name of
# a predicate having all variables as equal cards.
def getPredicatesWithAllVariablesBeingTheSameEqualCard():
    answers = set()
    for eq in getEquationsFromAllStratums():
        if (eq.leftVariable.id not in GenerationData.answersToStore) and\
                len(set(eq.leftArguments)) == 1 and\
                eq.type == 2:
            answers.add(eq.leftVariable.id)
    return answers

def getPredicatesWithAllVariablesBeingInTheSharedSet():
    answers = set()
    for eq in getEquationsFromAllStratums():
        if (eq.leftVariable not in GenerationData.answersToStore and \
                eq.type == 2 and
                len(set(eq.consultingArguments)) == len(eq.commonVariables)):
            answers.add(eq.consultingPredicate.id)
    return answers

def getPredicatesWithAllVariablesBeingInTheSharedSetIncludingConstants():
    answers = set()
    for eq in getEquationsFromAllStratums():
        if (eq.leftVariable.id not in GenerationData.answersToStore and \
                eq.type == 2):
            argument_constants = [x for x in eq.consultingArguments if isinstance(x, int) or  
                                    (isinstance(x, Argument) and x.type == "constant")]
            
            if len(eq.consultingArguments) == len(argument_constants):
                answers.add(eq.consultingPredicate.id)
                
    return answers

def getNegatedPredicates():
    answers = set()
    for eq in getEquationsFromAllStratums():
        for negated_element in eq.negatedElements:
            answers.add(negated_element.id )
    
    return answers


# This function get the solutions of the Datalog program. It returns a set
# containing the union of all the answers that must be stored represented by the 
# set of answersToStore and all the predicates having all its variables being 
# the same equal card. Also all the predicates that belong to a rule of type 2
# and all its variables are in the set of the Common variables are required to
# be considered solutions.
def getAllSolutions():
    solutions = set()
    solutions |= GenerationData.answersToStore
    solutions |= getPredicatesWithAllVariablesBeingTheSameEqualCard()
    solutions |= getPredicatesWithAllVariablesBeingInTheSharedSet()
    solutions |= getPredicatesWithAllVariablesBeingInTheSharedSetIncludingConstants()
    solutions |= getNegatedPredicates()
    return solutions

def getAllConsultingPredicates():
    return set(eq.consultingPredicate.id for eq in
                    getEquationsFromAllStratums() if eq.type == 2)
    
# This function returns a list containing tuples in which the first element
# is a predicate name and the second element is its length.
def getAllPredicatesLengths():
    data = []
    for eq in getEquationsFromAllStratums():
        data.append((eq.leftVariable.id,
                     len(eq.leftArguments)))
        data.append((eq.rightVariable.id,
                     len(eq.rightArguments)))

    # Remove duplicates
    return set(data)

# Auxiliary function to emit code to get a node. If a node doesn't exist the functions
# emit code to return return_value which must be a string with the wanted returned value
def emitCodeDataStructureGetNodeWithReturnValue(outfile, length, spaces_level, return_value):
    for x in xrange(1, length):
        level_str = 'root'
        if x > 1:
            level_str = 'n{}->level{}'.format(x, x + 1)
            
        node_str = 'node'
        if (x + 1) != length:
            node_str = 'n{}'.format(x + 1)
            
        outfile.write('{}Node{} *{};\n'.format(SPACES * spaces_level,
                                             x + 1,
                                             node_str))
        outfile.write('{}if (!{}.contains(x_{}))\n{}return {};\n'.format(SPACES * spaces_level,
                                                                        level_str,
                                                                        x,
                                                                        SPACES * (spaces_level + 1),
                                                                        return_value))
        outfile.write('{}else\n{}{} = {}.find(x_{});\n\n'.format(SPACES * spaces_level,
                                                                 SPACES * (spaces_level + 1),
                                                                 node_str,
                                                                 level_str,
                                                                 x))
        
        
# Auxiliary function to emit code to get a node. If a node doesn't exist the functions
# emit code to create a new node and attach it to the Data Structure
def emitCodeDataStructureGetNodeCreateIfDoesntExist(outfile, length, spaces_level):
    for x in xrange(1, length):
        level_str = 'root'
        lock_str = 'hashmap_lock'
        if x > 1:
            level_str = 'n{}->level{}'.format(x, x + 1)
            lock_str = 'n{}->hashmap_lock'.format(x)
            
        node_str = 'node'
        if (x + 1) != length:
            node_str = 'n{}'.format(x + 1)
            
        outfile.write('{}Node{} *{} = NULL;\n'.format(SPACES * spaces_level,
                                                          x + 1,
                                                          node_str))
        outfile.write("{}{}.find(x_{}, {});\n".format(SPACES * spaces_level,
                                                      level_str,
                                                      x,
                                                      node_str))
        outfile.write('{}if (!{}) {{\n'.format(SPACES * spaces_level, node_str))
        outfile.write('{}{}.lock();\n'.format(SPACES * (spaces_level + 1), lock_str))
        outfile.write("{}{}.find(x_{}, {});\n".format(SPACES * (spaces_level + 1),
                                                      level_str,
                                                      x,
                                                      node_str))
        outfile.write('{}if (!{}) {{\n'.format(SPACES * (spaces_level + 1), node_str))
        outfile.write('{}{} = new Node{}();\n'.format(SPACES * (spaces_level + 2),
                                                      node_str,
                                                      x + 1))                      
        outfile.write('{}{}.insert(x_{}, {});\n'.format(SPACES * (spaces_level + 2),
                                                          level_str,
                                                          x,
                                                          node_str))
        outfile.write('{}}}\n'.format(SPACES * (spaces_level + 1)))
        outfile.write('{}{}.unlock();\n'.format(SPACES * (spaces_level + 1), lock_str))
        outfile.write('{}}}\n\n'.format(SPACES * spaces_level))
        
# This function emits code for the definition of the axuiliary lists that are used to navigate
# through the sets of the data structure. 
@check_for_predicates_of_type2
def fillIntList(outfile, spaces):
    # Check if there is a rule without common variables if that is the case we
    # need to iterate over the first level of the data structure at some point
    # and we need an extra variable to deal with it as we don't store list
    # of integers for the first level.
    requires_t0 = any(len(x.commonVariables) == 0 for x in getEquationsFromAllStratums() if x.type == 2)
    # Obtain the number of variables we have to iterate over to generate new 
    # answers. That value is the number of variables in the consulting values list
    length = max(len(filter(lambda y: isinstance(y, Argument) and y.type == 'variable', x.consultingArguments)) 
                    for x in getEquationsFromAllStratums() if x.type == 2)
    
    # In case there is a rule with no common variables
    if requires_t0:
        #outfile.write('{}int t0;\n'.format(SPACES * 3))
        # Check if the longest length comes from a rule with no common variables
        # if that is the case then we have to subtract 1 to the value as we are already 
        # using t0. 
        no_cvars_max_length = max(len(filter(lambda y: isinstance(y, Argument) and y.type == 'variable', x.consultingArguments)) 
                                  for x in getEquationsFromAllStratums() if x.type == 2 and len(x.commonVariables) == 0)
        
        # At this point we now there are rules with no common variables but might be the case that there are no rules
        # with common variables so we have to make sure we can execute max on the sequence as it throws an exception if
        # it is run on an empty sequence
        cvars_max_length = 0
        cvars_max_length_list = [len(filter(lambda y: isinstance(y, Argument) and y.type == 'variable', x.consultingArguments)) 
                                  for x in getEquationsFromAllStratums() if x.type == 2 and len(x.commonVariables)]
        if len(cvars_max_length_list):
            cvars_max_length = max(cvars_max_length_list)
        
        if no_cvars_max_length == length and no_cvars_max_length > cvars_max_length:
            length -= 1
            
    # If in the end the length is 0 that means that the intList will be empty. In that
    # case doesn't make too much sense to emit code for it as it would only trigger a
    # warning from the c compiler
    if length > 0:
        l_args = ', '.join(['*l{}'.format(x + 1) for x in xrange(length)])
        outfile.write('{}LockedVectorInt {};\n'.format(spaces, l_args))


def fillRewritingVariable(outfile):
    max_length = max(chain((len(x.leftArguments) for x in getEquationsFromAllStratums()), 
                           (len(x.rightArguments) for x in getEquationsFromAllStratums())))
    predicate_ids_lengths = map(lambda x: (x.name.upper(), getPredicateLength(x)), getAllPredicatesIDs())
    
    outfile.write('class RewritingVariable {\n\n')
    outfile.write('public:\n')
    outfile.write('{}VariableType v_type;\n'.format(SPACES))
    outfile.write('{}int * values;\n\n'.format(SPACES))
    
    outfile.write('{}RewritingVariable(){{\n'.format(SPACES))
    outfile.write('{}this->v_type = VariableType::NONE;\n'.format(SPACES * 2))
    outfile.write('{}this->values = NULL;\n'.format(SPACES * 2))
    outfile.write('{}}}\n\n'.format(SPACES))
    
    for level_length in xrange(1, max_length + 1):
        #level_ids_length = filter(lambda x: x[1] == level_length, predicate_ids_lengths)
        # Check that at least we have a predicate whose length matches the current length otherwise
        # this function would never be called
        if not filter(lambda x: x[1] == level_length, predicate_ids_lengths):
            continue

        n_vars = ', '.join('int var{}'.format(x) for x in xrange(1, level_length + 1))
        outfile.write('{}RewritingVariable(VariableType v_type, {}){{\n'.format(SPACES, n_vars))
        outfile.write('{}this->v_type = v_type;\n'.format(SPACES * 2))
        outfile.write('{}this->values = new int[{}];\n\n'.format(SPACES * 2, level_length))
        for x in xrange(level_length):
            outfile.write('{}this->values[{}] = var{};\n'.format(SPACES * 2, x, x + 1))
        
        # This piece of code is just in case we need to identify the variables inside each level
        # because we can only use one function currently not needed as we are using polimorfic
        # constructors
        #for name, length in level_ids_length:
        #    outfile.write('{}if (v_type == VariableType.{}){{\n'.format(SPACES * 2, name))
        #    outfile.write('{}this.values = new int[{}];\n'.format(SPACES * 3, length))
        #    for x in xrange(length):
        #        outfile.write('{}this.values[{}] = var{};\n'.format(SPACES * 3, x, x + 1))
        #    outfile.write('{}}}\n'.format(SPACES * 2))
            
        outfile.write('{}}}\n\n'.format(SPACES))
    outfile.write('};')
    
def fillViews(outfile):
    # This instruction obtains all view names from all different stratums (in a set to avoid duplicates)
    view_names = set(chain.from_iterable(map(lambda x: x.keys(), 
                                             map(lambda x: x.viewNamesToCombinations,
                                                 getViewsFromAllStratums()))))
    
    outfile.write('class Views {\n\n')
    outfile.write('public:\n')
    for x, view_name in enumerate(view_names):
        outfile.write('{} const static int {} = {};\n'.format(SPACES, view_name, x))
    outfile.write('};\n')
    
def fillVariableType(outfile):
    # This instruction obtains all the predicate ids from all different stratums (in a set to avoid duplicates)
    predicate_ids = getAllPredicatesIDs()
    predicate_ids_str = ', '.join('{}'.format(name) for name in map(lambda x: x.name.upper(),
                                                                    predicate_ids))
    outfile.write('enum class VariableType: int {\n')
    outfile.write('{}NONE=0, {}\n}};\n'.format(SPACES, predicate_ids_str))


def fillDataStructureCreateNodeStructs(outfile):
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    lengths = list(xrange(number_of_data_structure_nodes, 1, -1))
    
    # Store the answers by length. This will be used to know in which level node store the
    # answers
    lengthToPreds = defaultdict(set)
    for eq in getEquationsFromAllStratums():
        if len(eq.rightArguments) > 1:
            lengthToPreds[len(eq.rightArguments)].add(eq.rightVariable.id)
        if len(eq.leftArguments) > 1:
            lengthToPreds[len(eq.leftArguments)].add(eq.leftVariable.id)
        for negated_element in eq.negatedElements:
            if len(negated_element.arguments) > 1:
                lengthToPreds[(len(negated_element.arguments))].add(negated_element.id)

    for length in lengths:
        view_names = map(lambda x: x[0], 
                         filter(lambda x: length <= len(x[1]),
                                viewNamesToCombinations.items()))
        solution_names = map(lambda x: x[0],
                             filter(lambda x: x in getAllSolutions(), 
                                    lengthToPreds[length]))
        outfile.write('{}struct Node{} {{\n'.format(SPACES, length))
        
        # Are we in the last level?
        # Otherwise we need a link to the next level. This is represented as a dict 
        if length != number_of_data_structure_nodes:
            outfile.write('{0}cuckoohash_map<unsigned int, Node{1}*> level{1};\n'.format(SPACES * 2, length + 1))
            outfile.write('{0}std::mutex hashmap_lock;\n'.format(SPACES * 2))
            outfile.write('\n')
            
        for view_name in view_names:
            outfile.write('{}LockedVectorInt {};\n'.format(SPACES * 2, view_name))
          
        outfile.write('\n')
          
        for solution_name in solution_names:
            outfile.write('{}LockedBitSet solution_{};\n'.format(SPACES * 2, solution_name))
        
        outfile.write('{}}};\n\n'.format(SPACES))
        
def fillDataStructureRootData(outfile):
    root_hashtable = (getDataStructureNodesMaximumLength() > 1)
    answers_of_length_1 = set()
    predicates_in_rules_of_length_1 = set()
    for equation in getEquationsFromAllStratums():
        if len(equation.rightArguments) == 1:
            answers_of_length_1.add(equation.rightVariable.id)
        if equation.type == 2 and len(equation.leftArguments) == 1:
            predicates_in_rules_of_length_1.add(equation.leftVariable.id)
        for negated_element in equation.negatedElements:
            if len(negated_element.arguments) == 1:
                answers_of_length_1.add(negated_element.id)

    
    if root_hashtable:
        outfile.write('{}LockedVectorInt empty_list;\n'.format(SPACES))
        outfile.write('{}cuckoohash_map<unsigned int, Node2*> root;\n'.format(SPACES))
        outfile.write('{}std::mutex hashmap_lock;\n'.format(SPACES))
    
    for pos, variable_id in enumerate(answers_of_length_1.union(predicates_in_rules_of_length_1)):
        if pos == 0 and root_hashtable:
            outfile.write('\n')
                        
        outfile.write('{}LockedBitSet R_{};\n'.format(SPACES,
                                                      variable_id.name))

def fillDataStructureHeaders(outfile):
    @check_for_predicates_of_type2
    def print_functions_for_type2_rules(outfile):
        viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
        lengths = xrange(getQueryMinimumLength(), getQueryMaximumLength()+1)
        for length in lengths:
            if length == 1:
                outfile.write('{}void insert_1(int);\n'.format(SPACES))
                continue
            args_to_function = ('int x_{}'.format(str(v+1)) for v in xrange(length))
            outfile.write('{}void insert{}(int pos, {});\n'.format(SPACES,
                                                                   length,
                                                                   ", ".join(args_to_function)))
    
        outfile.write('\n')
        
        lengths = xrange(2, getQueryMaximumLength()+1)
        for length in lengths:
            if length == 1: continue
            args_to_function = ('int x_{}'.format(str(v+1)) for v in xrange(length - 1))
            outfile.write('{}LockedVectorInt* get{}(int pos, {});\n'.format(SPACES,
                                                                            length,
                                                                            ", ".join(args_to_function)))
        outfile.write('\n')
        
    root_hashtable = (getDataStructureNodesMaximumLength() > 1)
    if root_hashtable:
        outfile.write('{}std::vector<unsigned int> get_level0_values();\n\n'.format(SPACES))
        
    print_functions_for_type2_rules(outfile)
    
    for variable_id in getAllSolutions():
        length = getPredicateLength(variable_id)
        args = ', '.join('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('{}bool check_and_update_solution_{}({});\n'.format(SPACES,
                                                                          variable_id.name,
                                                                          args))
        outfile.write('{}bool contains_solution_{}({});\n'.format(SPACES,
                                                                  variable_id.name,
                                                                  args))
        outfile.write('{}void append_solution_{}({});\n'.format(SPACES,
                                                                variable_id.name,
                                                                args))
        
        outfile.write('\n')

    
@check_for_predicates_of_type2
def fillDataStructureInsertFunctions(outfile):
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    lengths = xrange(getQueryMinimumLength(), getQueryMaximumLength()+1)
    root_hashtable = (getDataStructureNodesMaximumLength() > 1)
    
    for length in lengths:
        # We have to handle length 1 differently. If we detect that the current length is 1 as we don't
        # have a level 1 node for the data structure we have to emit code differently that is why the
        # auxiliary function code_for_Ds_insert_1 is invoked and then we continue the to the next length.
        # We do it in this way as is easier to create an auxiliary function for this case that to add
        # checks for the control flow to detect if we are in the length 1 case every time we emit code.
        if length == 1:
            outfile.write('void Datastructure::insert_1(int x_1) {\n')
            
            if root_hashtable:
                outfile.write('{}Node2 *node=NULL;\n'.format(SPACES))
                outfile.write('{}root.find(x_1, node);\n'.format(SPACES))
                outfile.write('{}if (!node) {{\n'.format(SPACES))
                outfile.write('{}hashmap_lock.lock();\n'.format(SPACES * 2))
                outfile.write('{}root.find(x_1, node);\n'.format(SPACES * 2))
                outfile.write('{}if (!node) {{\n'.format(SPACES * 2))
                outfile.write('{}root.insert(x_1, new Node2());\n'.format(SPACES * 3))
                outfile.write('{}}}\n'.format(SPACES * 2))
                outfile.write('{}hashmap_lock.unlock();\n'.format(SPACES * 2))
                outfile.write('{}}}\n'.format(SPACES))
                
            outfile.write('}\n\n')
            continue
        
        view_names = map(lambda x: x[0], 
                         filter(lambda x: len(x[1]) == length,
                                viewNamesToCombinations.items()))
        
        # We don't have views of the current length so we don't need to generate the code
        if not len(view_names):
            continue
        
        args_to_function = ('int x_{}'.format(str(v+1)) for v in xrange(length))
        outfile.write('void Datastructure::insert{}(int pos, {}) {{\n'.format(length,
                                                                              ", ".join(args_to_function)))
        
        # Get the Node that we need
        emitCodeDataStructureGetNodeCreateIfDoesntExist(outfile, length, 1)
            
        for x, view_name in enumerate(view_names, start = 1):
            cond_keyword = 'if'
            cond_condition = ' (pos == Views::{})'.format(view_name)
            if x > 1:
                if x < len(view_names):
                    cond_keyword = 'else if'
                else:
                    cond_keyword = 'else'
                    cond_condition = ''
                
            outfile.write('{}{}{} {{\n'.format(SPACES, cond_keyword, cond_condition))
            for x in xrange(2, length+1):
                if x != length:
                    outfile.write('{}n{}->{}.lock();\n'.format(SPACES * 2, x, view_name))
                    outfile.write('{}n{}->{}.add(x_{});\n'.format(SPACES * 2, x, view_name, x))
                    outfile.write('{}n{}->{}.unlock();\n'.format(SPACES * 2, x, view_name))
                    outfile.write('\n')
                else:
                    outfile.write('{}node->{}.lock();\n'.format(SPACES * 2, view_name))
                    outfile.write('{}node->{}.add(x_{});\n'.format(SPACES * 2, view_name, x))
                    outfile.write('{}node->{}.unlock();\n'.format(SPACES * 2, view_name))
            outfile.write('{}}}\n'.format(SPACES))
            
        outfile.write('}\n\n')

@check_for_predicates_of_type2
def fillDataStructureGetLevel0Values(outfile):
    root_hashtable = (getDataStructureNodesMaximumLength() > 1)
    
    if not root_hashtable:
        return 
    
    outfile.write('std::vector<unsigned int> Datastructure::get_level0_values() {\n')
    outfile.write('{}std::vector<unsigned int> results;\n\n'.format(SPACES))
    outfile.write('{}for (const auto &it: root.lock_table())\n'.format(SPACES))
    outfile.write('{}results.push_back(it.first);\n\n'.format(SPACES * 2))    
    outfile.write('{}return results;\n'.format(SPACES))
    outfile.write('}\n')

@check_for_predicates_of_type2
def fillDataStructureGetFunctions(outfile):
    lengths = xrange(2, getQueryMaximumLength()+1)
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    
    for length in lengths:
        args_to_function = ('int x_{}'.format(str(v+1)) for v in xrange(length - 1))
        outfile.write('LockedVectorInt* Datastructure::get{}(int pos, {}) {{\n'.format(length,
                                                                                            ", ".join(args_to_function)))
        
        # Get the Node that we need
        emitCodeDataStructureGetNodeWithReturnValue(outfile, length, 1, '&empty_list')
        
        outfile.write('\n')
        
        
        view_names = map(lambda x: x[0], 
                         filter(lambda x: length <= len(x[1]),
                                viewNamesToCombinations.items()))
        
        # Return the required view
        for x, view_name in enumerate(view_names, start = 1):
            cond_keyword = 'if'
            cond_condition = ' (pos == Views::{})'.format(view_name)
            if x > 1:
                if x < len(view_names):
                    cond_keyword = 'else if'
                else:
                    cond_keyword = 'else'
                    cond_condition = ''
                
            outfile.write('{}{}{}\n'.format(SPACES, cond_keyword, cond_condition))
            outfile.write('{}return &node->{};\n'.format(SPACES * 2, view_name))
            
        if x == 1:
            outfile.write('\n{}return &empty_list;\n'.format(SPACES, view_name))
            
        outfile.write('}\n\n')
        
def fillDataStructureContainsSolutionFunctions(outfile):
    for variable_id in getAllSolutions():
        length = getPredicateLength(variable_id)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('bool Datastructure::contains_solution_{}({}) {{\n'.format(variable_id.name,
                                                                                 ', '.join(args)))
        
        if length == 1:
            outfile.write('{}return R_{}.test(x_1);\n'.format(SPACES, variable_id.name))
            outfile.write('}\n\n')
            continue
        
        # Get the Node that we need
        emitCodeDataStructureGetNodeWithReturnValue(outfile, length, 1, 'false')
        
        outfile.write('\n')
        
        outfile.write('{}return (node->solution_{}.test(x_{}));\n'.format(SPACES,
                                                                         variable_id.name,
                                                                         length))
        outfile.write('}\n\n')
        
        
def fillDataStructureAppendSolutionFunctions(outfile):
    for variable_id in getAllSolutions():
        length = getPredicateLength(variable_id)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('void Datastructure::append_solution_{}({}) {{\n'.format(variable_id.name,
                                                                               ', '.join(args)))
        
        if length == 1:
            outfile.write('{}R_{}.lock();\n'.format(SPACES, variable_id.name))
            outfile.write('{}R_{}.set(x_1);\n'.format(SPACES, variable_id.name))
            outfile.write('{}R_{}.unlock();\n'.format(SPACES, variable_id.name))
            outfile.write('}\n\n')
            continue
        
        # Get the Node that we need
        emitCodeDataStructureGetNodeCreateIfDoesntExist(outfile, length, 1)
        
        outfile.write('{}node->solution_{}.set(x_{});\n'.format(SPACES,
                                                               variable_id.name,
                                                               length))
        outfile.write('}\n\n')
        
def fillDataStructureCheckAndUpdateFunctions(outfile):
    for variable_id in getAllSolutions():
        length = getPredicateLength(variable_id)
        
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('bool Datastructure::check_and_update_solution_{}({}) {{\n'.format(variable_id.name,
                                                                                           ', '.join(args)))
        outfile.write('{}bool r = false;\n\n'.format(SPACES))
        
        if length == 1:
            outfile.write('{}R_{}.lock();\n'.format(SPACES, variable_id.name))
            outfile.write('{}if (!R_{}.test(x_1)) {{\n'.format(SPACES, variable_id.name))
            outfile.write('{}R_{}.set(x_1);\n'.format(SPACES * 2, variable_id.name))
            outfile.write('{}r = true;\n'.format(SPACES * 2))
            outfile.write('{}}}\n'.format(SPACES))
            outfile.write('{}R_{}.unlock();\n\n'.format(SPACES, variable_id.name))
            outfile.write('{}return r;\n'.format(SPACES))
            outfile.write('}\n\n')
            continue
        
        # Get the Node that we need
        emitCodeDataStructureGetNodeCreateIfDoesntExist(outfile, length, 1)
        
        outfile.write('{}node->solution_{}.lock();\n'.format(SPACES,
                                                            variable_id.name))
        outfile.write('{}if (!node->solution_{}.test(x_{})) {{\n'.format(SPACES,
                                                                       variable_id.name,
                                                                       length))
        outfile.write('{}node->solution_{}.set(x_{});\n'.format(SPACES * 2,
                                                               variable_id.name,
                                                               length))
        outfile.write('{}r = true;\n'.format(SPACES * 2))
        outfile.write('{}}}\n'.format(SPACES))
        outfile.write('{}node->solution_{}.unlock();\n\n'.format(SPACES,
                                                                 variable_id.name))
        outfile.write('{}return r;\n'.format(SPACES))
        outfile.write('}\n\n')
        
def fillSolverPrivateDataAndFunctions(outfile):
    number_of_stratums = len(GenerationData.stratums)
    
    # Data
    outfile.write("{}int num_threads;\n".format(SPACES))
    outfile.write("{}Datastructure data;\n".format(SPACES))
    
    # Functions for the stratums
    for stratum_level in xrange(1, number_of_stratums + 1):
        negated_predicates = any(eq.negatedElements for eq in GenerationData.stratums[stratum_level-1].equations)
        
        if not negated_predicates:
            outfile.write('{}void init_stratum_{}(std::list<RewritingVariable>[]);\n'.format(SPACES, stratum_level))
        else:
            outfile.write('{}void init_stratum_{}(std::list<RewritingVariable>[], Datastructure &);\n'.format(SPACES, 
                                                                                                               stratum_level))
            
        outfile.write('{}static void compute_stratum_{}(int, '.format(SPACES, stratum_level))
        queues_args = ''
        if stratum_level < number_of_stratums:
            queues_args = ', '.join('std::list<RewritingVariable> *' for _ in xrange(stratum_level, number_of_stratums))
            outfile.write('std::list<RewritingVariable> *, Datastructure *, {});\n\n'.format(queues_args))
        else:
            outfile.write('std::list<RewritingVariable> *, Datastructure *);\n\n')
    
def fillSolverWriteRewritingVariable(outfile):
    allPredicates = getAllPredicatesIDs()
    
    outfile.write('void write_rewriting_variable(std::ofstream &fp, RewritingVariable &r) {\n')
    outfile.write('{}std::string s;\n\n'.format(SPACES))
    
    for pos, predicate in enumerate(allPredicates):
        if_str = 'if'
        if_cond = ' (r.v_type == VariableType::{})'.format(predicate.name.upper())
        if pos == len(allPredicates) - 1:
            if_str = 'else'
            if_cond = ''
        elif pos > 0:
            if_str = 'else if'
        
        
        values_args = ' + std::string(", ") + '.join('std::to_string(r.values[{}])'.format(x) 
                                                     for x in xrange(getPredicateLength(predicate)))
        outfile.write('{}{}{} {{\n'.format(SPACES, if_str, if_cond))
        outfile.write('{}s = std::string("{}(") + {} + std::string(").\\n");\n'.format(SPACES * 2,
                                                                                       predicate.name,
                                                                                       values_args))
        outfile.write('{}}}\n'.format(SPACES))
    outfile.write('\n')
    
    outfile.write('{}fp.write(s.c_str(), s.length());\n'.format(SPACES))
    
    outfile.write('}\n')
        

def fillSolverInitFunction(outfile):
    outfile.write('bool Solver::init(int num_threads) {\n')
    outfile.write('{}this->num_threads = num_threads;\n'.format(SPACES))
    
    outfile.write('\n{}return true;\n'.format(SPACES))
    outfile.write('}\n')
    
def fillSolverEndFunction(outfile):
    outfile.write('bool Solver::end() {\n')
        
    outfile.write('{}return true;\n'.format(SPACES))
    outfile.write('}\n')
        
def fillSolverComputeFunction(outfile):
    number_of_stratums = len(GenerationData.stratums)
    
    outfile.write('bool Solver::compute() {\n')
    
    if number_of_stratums > 1:
        outfile.write('{}int queue_id;\n'.format(SPACES))
        
    outfile.write('{}std::list<RewritingVariable> queues[num_threads];\n'.format(SPACES))
    for x in xrange(2, number_of_stratums + 1):
        outfile.write('{}std::list<RewritingVariable> queue_stratum_{};'.format(SPACES, x))
    outfile.write('{}std::thread threads[num_threads];\n\n'.format(SPACES))
    
   
    for stratum in xrange(1, number_of_stratums + 1):
        negated_predicates = any(eq.negatedElements for eq in GenerationData.stratums[stratum-1].equations)
        
        outfile.write('{}/* Stratum  {} */\n'.format(SPACES, stratum))
        
        if stratum > 1:
            outfile.write('{}queue_id = 0;\n'.format(SPACES))
            outfile.write('{}while (!queue_stratum_{}.empty()) {{\n'.format(SPACES, stratum))
            outfile.write('{}queues[queue_id].push_back(queue_stratum_{}.front());\n'.format(SPACES * 2, stratum))
            outfile.write('{}queue_stratum_{}.pop_front();\n'.format(SPACES * 2, stratum))
            outfile.write('{}queue_id = (queue_id + 1) % num_threads;\n'.format(SPACES * 2, stratum))
            outfile.write('{}}}\n'.format(SPACES))
        
        if not negated_predicates:
            outfile.write('{}init_stratum_{}(queues);\n\n'.format(SPACES, stratum))
        else:
            outfile.write('{}init_stratum_{}(queues, data);\n\n'.format(SPACES, stratum))
            
        outfile.write('{}for (int i = 0; i < num_threads; i++) {{\n'.format(SPACES))
        other_stratum_queues = ', '.join(['&queue_stratum_{}'.format(x) for x in xrange(stratum + 1, number_of_stratums + 1)])
        if other_stratum_queues:
            outfile.write('{}threads[i] = std::thread(compute_stratum_{}, i + 1, &queues[i], &data, {});\n'.format(SPACES * 2,
                                                                                                               stratum,
                                                                                                               other_stratum_queues))
        else:
            outfile.write('{}threads[i] = std::thread(compute_stratum_{}, i + 1 , &queues[i], &data);\n'.format(SPACES * 2,
                                                                                                           stratum))
        outfile.write('{}}}\n\n'.format(SPACES))

        outfile.write('{}for (int i = 0; i < num_threads; i++) {{\n'.format(SPACES))
        outfile.write('{}threads[i].join();\n'.format(SPACES * 2));
        outfile.write('{}}}\n\n'.format(SPACES))
    
    outfile.write('{}return true;\n'.format(SPACES))
    outfile.write('}\n')
    
def fillSolverInitStratumFunctions(outfile):
    extensional = list(getExtensionalPredicates())
    extensional_as_set = set(extensional)
    idToStratumLevels = GenerationData.idToStratumLevels
    number_of_stratums = len(GenerationData.stratums)
        
    # Create a new dictionary from idToStratumLevels only containing
    # extensional predicates
    extensionalToStratumLevels = {k: v for (k,v) in idToStratumLevels.iteritems() if k in extensional_as_set}
    
    for stratum_level in xrange(1, number_of_stratums + 1):
        negated_predicates = any(eq.negatedElements for eq in GenerationData.stratums[stratum_level-1].equations)
        
        if not negated_predicates:
            outfile.write('void Solver::init_stratum_{}(std::list<RewritingVariable> queues[]) {{\n'.format(stratum_level))
        else:
            outfile.write('void Solver::init_stratum_{}(std::list<RewritingVariable> queues[], Datastructure &data) {{\n'.format(stratum_level))
            
        outfile.write('{}std::ifstream file;\n'.format(SPACES))
        outfile.write('{}std::string text;\n'.format(SPACES))
        outfile.write('{}int queue_id;\n\n'.format(SPACES))
        
        # Get the predicates that belong to the current stratum level
        idVars = (idVar for (idVar, levels) in extensionalToStratumLevels.iteritems()
                                if stratum_level in levels)
        
        # If we are in the first of the level we must honor the order of the block
        # as negated predicates must be put first
        if (stratum_level == 1):
            idsVarsSet = set(idVars)
            idVars = ( x for x in extensional if x in idsVarsSet )
            
        for idVar in idVars:
            predicate_length = getPredicateLength(idVar)
            outfile.write('{}/* {}.tuples file */\n'.format(SPACES, idVar.name))
            outfile.write('{}queue_id = 0;\n'.format(SPACES))
            outfile.write('{}file = std::ifstream("{}.tuples");\n'.format(SPACES, idVar.name))
            outfile.write('{}if (!file) {{\n'.format(SPACES))
            outfile.write('{}std::cerr << "Solver Error::Can\'t open file \'{}.tuples\'." << std::endl;\n'.format(SPACES * 2,
                                                                                                                  idVar.name))
            outfile.write('{}exit(0);\n'.format(SPACES * 2))
            outfile.write('{}}}\n\n'.format(SPACES))
            
            outfile.write('{}while (std::getline(file, text)) {{\n'.format(SPACES))
            # The next line of java code has been split into two different output lines due to its length
            outfile.write('{}std::vector<std::string> numbers = split(text.substr(text.find(\'(\')+1,'.format(SPACES * 2))
            outfile.write('text.find(\')\')), \',\');\n')
            for var_num in xrange(1, predicate_length + 1):
                outfile.write('{}int var{} = std::stoi(numbers[{}]);\n'.format(SPACES * 2,
                                                                                 var_num,
                                                                                 var_num - 1))
            
            outfile.write('\n')
            vars_list = ('var{}'.format(x) for x in xrange(1, predicate_length + 1))
            
            if not (idVar in getNegatedPredicates()):
                # The next line of java code has been split into two different output lines due to its length
                outfile.write('{}queues[queue_id].push_back(*(new '.format(SPACES * 2, idVar.name))
                outfile.write('RewritingVariable(VariableType::{}, {})));\n'.format(idVar.name.upper(),
                                                                                    ', '.join(vars_list)))
                outfile.write('{}queue_id = (queue_id + 1) % num_threads;\n'.format(SPACES * 2))
            else:
                outfile.write('{}data.append_solution_{}({});\n'.format(SPACES * 2,
                                                                        idVar.name,
                                                                        ', '.join(vars_list)))
            outfile.write('{}}}\n'.format(SPACES))
            outfile.write('{}file.close();\n'.format(SPACES))
        outfile.write('}\n')

def fillSolverComputeStratumClasses(outfile):
    # Auxiliary function used to obtain the index position of a querying argument.
    # It is the position of the argument has on the elements we query to the database.
    def get_t_index(argument, consulting_arguments, common_variables):
        return consulting_arguments.index(argument) + 1\
            - len(common_variables) - len([ x for x in consulting_arguments if
                                           isinstance(x, Argument) and x.type == 'constant' ])
    
    # Auxiliary function that returns the string to be emitted when we detect an
    # argument that is a variable. It returns the code required to query the 
    # database using the given variable.
    # Parameters:
    #    argument -> The argument we want to emit code for. Its type must be 'variable'.
    # consulting_arguments -> A list with the consulting arguments of the equation.
    #     common_variables -> A list with the common_variables of the equation.
    def compose_argument_variable(argument, consulting_arguments, common_variables):
        emitting_code = ''
        t_index = get_t_index(argument,
                              consulting_arguments,
                              common_variables)
        if len(common_variables) == 0:
            if t_index == 1:
                emitting_code += "t0"
            else:
                emitting_code += "t{}".format(t_index-1)
        else:
            emitting_code += "t{}".format(t_index)
            
        return emitting_code        

    # Auxiliary function that returns the string to be emitted when we detect an
    # expression.
    # Parameters:
    #    expression -> The expression from which we desire to emmit the code. 
    #                  (Can have different types check the source code).
    # consulting_arguments -> A list with the consulting arguments of the equation.
    #     common_variables -> A list with the common_variables of the equation.
    def compose_expression(expression, consulting_arguments, common_variables):
        if isinstance(expression, int):
            return "current.values[{}]".format(expression - 1)
        elif isinstance(expression, Argument) and expression.type == 'constant':
            return str(expression.value)
        elif isinstance(expression, Argument) and expression.type == 'variable':
            return compose_argument_variable(expression,
                                    consulting_arguments,
                                    common_variables)
        elif isinstance(expression, ArithmeticExpression):
            args, op = expression
            emitting_code = ''
                    
            for x in xrange(2):
                if isinstance(args[x], int):
                    emitting_code += "current.values[{}]".format(args[x] - 1)
                elif isinstance(args[x], Argument):
                    if args[x].type == "constant":
                        emitting_code += str(args[x].value)
                    elif args[x].type == 'variable':
                        emitting_code += compose_argument_variable(args[x], 
                                                          consulting_arguments, 
                                                          common_variables)
                    else:
                        error_msg = "Emmiting code for an assignation expresion (Unknown type): "
                        raise ValueError(error_msg + str(args[x]))
                else:
                    error_msg = "Emmiting code for an assignation expresion (Unknown type): "
                    raise ValueError(error_msg + str(args[x]))
                            
                if x == 0:
                    emitting_code += " " + op + " "
            
            return "(" + emitting_code + ")"
        else:
            error_msg = "Emmiting code (Unknown type): "
            raise ValueError(error_msg + str(expression))
        
    # This function emits code regardless we are dealing with a type 1 or type 2 rewriting equation.
    # Parameters:
    #  spaces -> A string. Representing the number of spaces that we have to print when emitting code.
    #  equation -> A RewritingRule1 or RewritingRule2. Represents the rewriting equation.
    # level -> An integer. Represents the stratum we are in.
    # num_of_stratums -> An integer. Represents the total number of stratums required by the 
    #                    Datalog program.
    # idToStratumLevels -> A dictionary. The dictionary is a mapping between the identifiers and
    #                      the stratum level they belong.
    #def common_block(spaces, equation, level, num_of_stratums, idToStratumLevels):
    def common_block(spaces, equation, level, num_of_stratums, args, idToStratumLevels):
        # Do we have to store the answer??
        if equation.rightVariable.id in answersToStore:
            variable_id = equation.rightVariable.id

            #args = ', '.join('var.values[{}]'.format(x) for 
            #                x in xrange(0, len(equation.rightArguments)))
            
            #outfile.write('{}if (data.check_and_update_solution_{}({}))'.format(spaces,
            #                                                                    variable_id.name,
            #                                                                    args))
            
            #outfile.write('{}if (data.check_and_update_solution_{}({}))'.format(spaces,
            #                                                                    variable_id.name,
            #                                                                    ', '.join(args[1:])))
            outfile.write('{}if ('.format(spaces))
            
            if equation.booleanExpressions:
                #outfile.write( ' &&\n{0}{1}'.format(spaces,
                #                                    '    '))
                boolean_expressions_str = ''
                for p1, (_, b_args, b_op) in enumerate(equation.booleanExpressions):
                    boolean_expression_str = ''
                    for p2, b_arg in enumerate(b_args):
                        side = ''

                        if equation.type == 1:
                            side = compose_expression(b_arg, None, None)
                        else:
                            side = compose_expression(b_arg,
                                                      equation.consultingArguments,
                                                      equation.commonVariables)
                            
                        boolean_expression_str += side

                        if p2 == 0:
                            boolean_expression_str += " " + b_op + " "
                            
                    boolean_expressions_str += "(" + boolean_expression_str + ")"
                    if p1 != len(equation.booleanExpressions) - 1:
                        boolean_expressions_str += " &&\n{}{}".format(spaces,
                                                                         '    ')
                        
                outfile.write(boolean_expressions_str)
            
            if equation.booleanExpressions and equation.negatedElements:
                outfile.write( ' &&\n')
            
            for (pos, negated_element) in enumerate(equation.negatedElements):
                negated_arguments_str = []

                for negated_arg in negated_element.arguments:
                    if negated_arg.type == 'constant':
                        negated_arguments_str.append(str(negated_arg.value))
                    else:
                        found = False
                        for argument, position in equation.leftArguments:
                            if negated_arg == argument:
                                negated_arguments_str.append('current.values[{}]'.format(position - 1))
                                found = True
                                break
                        if not found and equation.type == 2:
                            # HERE WE HAVE TWO OPTIONS WE CAN USE THE VAR FROM THE REWRITING
                            # VARIABLE (the commented piece of code) or THE T INDEX.
                            #for position, element in enumerate(equation.rightArguments, start=1):
                            #    if negated_arg == element:
                            #        negated_arguments_str.append('VAR.VAR_{}'.format(position))
                            negated_arguments_str.append(compose_argument_variable(negated_arg, 
                                                                          equation.consultingArguments,
                                                                          equation.commonVariables))
                    
                negated_spaces = ''        
                if (equation.booleanExpressions and equation.negatedElements) or pos > 1:
                    negated_spaces = spaces + '    '
                    
                
                negated_arguments = ', '.join(negated_arguments_str)
                outfile.write('{}!data->contains_solution_{}({}) &&\n'.format(negated_spaces,
                                                                             negated_element.id.name,
                                                                             negated_arguments))
                #if (pos != len(equation.negatedElements) - 1):
                #    outfile.write(' &&\n')
            spaces += SPACES
            
            if equation.booleanExpressions and not equation.negatedElements:
                outfile.write(' &&\n')
            
            if equation.negatedElements or equation.booleanExpressions:
                outfile.write('{}{}'.format(spaces, '    '))
              
            outfile.write('data->check_and_update_solution_{}({})) {{\n'.format(variable_id.name,
                                                                               ', '.join(args[1:])))
            
            # To compute a program a variable can be required to be evaluated in different queues, here we
            # make sure that the variable is added to every required queue. IdToStratums is a dictionary that
            # contains the required information to emit the code. It takes as a key a variable_id and returns
            # the queue levels in which is required.
            for queue_level in idToStratumLevels[variable_id]:
                #outfile.write('{}solver_queue->push_back(var);\n'.format(spaces))
                if queue_level == level:
                    outfile.write('{}solver_queue->push_back(*(new RewritingVariable(VariableType::{}, {})));\n'.format(spaces,
                                                                                                                args[0],
                                                                                                                ', '.join(args[1:])))
                else:
                    outfile.write('{}queue_stratum_{}->push_back(*(new RewritingVariable(VariableType::{}, {})));\n'.format(spaces,
                                                                                                                       queue_level,
                                                                                                                       args[0],
                                                                                                                       ', '.join(args[1:])))

        # TODO: What is this used for?
        else:
            outfile.write('{}solver_queue1.append(id, var);\n'.format(spaces))
            
        spaces = spaces[:-len(SPACES)]
        outfile.write('{}}}\n'.format(spaces))
        
    predsToViewNames = dict(chain(*[ view.predsToViewNames.items() for view in getViewsFromAllStratums() ]))
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    aliasToViewNames = dict(chain(*[ view.aliasToViewNames.items() for view in getViewsFromAllStratums() ]))
    answersToStore = GenerationData.answersToStore
    printVariables = GenerationData.printVariables
    outputTuples = GenerationData.answersToStore
    idToStratumLevels = GenerationData.idToStratumLevels
    number_of_stratums = len(GenerationData.stratums)
    
    spaces_level_1 = SPACES 
    spaces_level_2 = SPACES * 2
    spaces_level_3 = SPACES * 3
    
    # Here we emit code to handle the different stratums in the solver_compute function
    for level, stratum in enumerate(GenerationData.stratums, start=1):
        answerFileNames = map(lambda x: 'fp_' + x.name,
                              filter(lambda x: level == min(idToStratumLevels[x]),
                                     answersToStore))
        
        
        outfile.write('/* Stratum {} */\n'.format(level))
        
        # This line of java code has been splitted into different output lines because it is too long
        outfile.write('void Solver::compute_stratum_{} (int id, '.format(level))
        if (level + 1) <= number_of_stratums:
            queue_args = ', '.join('std::list<RewritingVariable> *queue_stratum_{}'.format(x) for x in xrange(level + 1, number_of_stratums + 1))
            outfile.write('std::list<RewritingVariable> *solver_queue, Datastructure *data, {}) {{\n'.format(queue_args))
        else:
            outfile.write('std::list<RewritingVariable> *solver_queue, Datastructure *data) {\n')

        #outfile.write('{}RewritingVariable current, var;\n\n'.format(spaces_level_3))
        fillIntList(outfile, spaces_level_1)
        outfile.write('{}RewritingVariable current;\n'.format(spaces_level_1))
        if answerFileNames:
            fileStratumAnswers_args = ', '.join(answerFileNames)
            outfile.write("{}std::ofstream {};\n".format(spaces_level_1, 
                                                         fileStratumAnswers_args))
        outfile.write('\n')
        
        if answerFileNames:
            outfile.write('{}// Output file streams\n'.format(spaces_level_1))
            for fname in answerFileNames:
                outfile.write('{}{}.open(std::string("{}-") + std::to_string(id) '.format(spaces_level_1, 
                                                                                          fname, 
                                                                                          fname[3:]))
                outfile.write('+ std::string(".tuples"), std::ios::out | std::ios::trunc);\n')
                outfile.write('{}if (!{}) {{\n'.format(spaces_level_1,
                                                       fname))
                outfile.write('{}std::cerr << "Solver Error:: Can\'t '.format(spaces_level_2))
                outfile.write('open file {}.tuples::Thread " << id << std::endl;\n'.format(fname[3:]))
                outfile.write('{}exit(0);\n'.format(spaces_level_2))
                outfile.write('{}}}\n'.format(spaces_level_1))
            outfile.write('\n')
        
        outfile.write('{}while (!solver_queue->empty()) {{\n'.format(spaces_level_1))
        # THIS LINE IS RELATED WITH THE STRATUMS ON THE SEQUENTIAL VERSION
        #outfile.write('{}current = solver_queue{}.poll()\n\n'.format(spaces_level_4,
        #                                                             level))
        outfile.write('{}current = solver_queue->front();\n'.format(spaces_level_2))
        outfile.write('{}solver_queue->pop_front();\n'.format(spaces_level_2))
        
        block1 = stratum.ordering.block1
        block2 = stratum.ordering.block2
        block3 = stratum.ordering.block3
    
        for variable_id in chain(block1, block2, block3):
            # Get the equation of the predicate raise an exception if not found
            equations = (x for x in getEquationsFromAllStratums() if x.leftVariable.id == variable_id)
    
            outfile.write('\n')
            outfile.write('{}/* Rewriting variable {} block */\n'.format(spaces_level_2, variable_id.name))
            outfile.write('{}if (current.v_type == VariableType::{})'.format(spaces_level_2,
                                                                             variable_id.name.upper()))
            outfile.write(' {\n')

            #if variable_id in outputTuples:
            #    outfile.write('{}write_rewriting_variable(fp_{}, current);\n\n'.format(spaces_level_3, variable_id.name))

            # The answer can be represented in more than one level (stratum). We need to 
            # assure that we only emit the answer once, otherwise the solution would appear 
            # as many times as it appears in the different level. In which level we store
            # the answer is meaningless but we have to make sure that we only do it once,
            # so we store in the first stratum the answer appears represented. To do this
            # we sort the levels the in which the variable appears take the first one and
            # check that is the level that the code is being emitted. 
            level_to_store_answer = sorted(idToStratumLevels[variable_id])[0]
            # Do we have to print the variable to stdout?.
#             if level == level_to_store_answer and variable_id in printVariables:
#                 outfile.write("{}print_answer(stdout, &current->b);\n".format(spaces_level_5))
                
            # Is it a solution? Then print it to a file.
            if level == level_to_store_answer and variable_id in outputTuples:
                outfile.write("{}write_rewriting_variable(fp_{}, current);\n".format(spaces_level_3,
                                                                                     variable_id.name))
            
            pred_length = getPredicateLength(variable_id)
            
            # Debug information
#             outfile.write('#ifdef NDEBUG\n')
#             formatting = ', '.join(['%i' for _ in xrange(pred_length)])
#             separator = ',\n{}'.format(spaces_level_5)
#             args = separator.join(('current->b.VAR_{}'.format(str(x+1)) for x in xrange(pred_length)))
#             output_string = '{}fprintf(stderr, "Handling rewriting '.format(spaces_level_3) +\
#                             'variable: X_{}'.format(variable_id.name) +\
#                             '({})\\n",\n{}{});\n'.format(formatting,
#                                                          spaces_level_5,
#                                                          args)
#             outfile.write(output_string)
            #outfile.write('#endif\n')
            
            # Here we emit code to add data to the data structure if we are in a type 2 equation.
            # Again we only store the variable to the database if we are in the first level (stratum)
            # the variable appears in.
            # We emit debugging code via a c macro to check what is going to be added
            # to the data structure. We show the view and the values being added.
            # After we use the appropriate call to add the solution to the data structure
#             if variable_id in predsToViewNames:
#                 # This is the debugging part
#                 #outfile.write('\n#ifdef NDEBUG\n')
#                   
#                 # Debug information: If the predicate has length 1 the it becomes a solution and has to be
#                 # treated as such. Otherwise we insert a value into the list as normal
#                 if (level == level_to_store_answer) and (pred_length == 1):
#                     outfile.write('{}fprintf(stderr, "\\tData structure: '.format(spaces_level_3))
#                     outfile.write('Adding solution {}(%i)\\n", current->b.VAR_1);\n'.format(variable_id.name))
#                 elif (level == level_to_store_answer):
#                     for view in predsToViewNames[variable_id]:
#                         args = ', '.join('current->b.VAR_{}'.format(x) for
#                                          x in viewNamesToCombinations[view])
#                         formatting = ', '.join(('%i' for _ in viewNamesToCombinations[view]))
#       
#                         outfile.write('{}fprintf(stderr, "\\tData structure: '.format(spaces_level_3))
#                         outfile.write('Adding {}({})\\n", {});\n'.format(view,
#                                                                         formatting,
#                                                                         args))
              
            # This marks the end of the debug information macro this line has to be always emitted as 
            # the portion of the handling the rewriting variable is always emitted and only the
            # adding solution is optional if the predicate is part of a type 2 equation that is there is     
            # a view associated with it
#             outfile.write('#endif\n')
            
            # Unfortunately because of the problem of the previous line we have to recheck here if the
            # predicate has a view associated with it
            if variable_id in predsToViewNames:     
                # This is part in which we add the solution to the data structure. If the predicate has length
                # 1 we have to add directly the solution, as by convention there is no level node of length 0
                # and the predicates of length 1 are turned into solutions
                if (level == level_to_store_answer) and (pred_length == 1):
                    outfile.write('{}data->append_solution_{}(current.values[0]);\n'.format(spaces_level_3,
                                                                                                    variable_id.name))
                    # If the variable only appears as a negated predicate we don't have to insert it to the database
                    if variable_id in getAllConsultingPredicates():
                        outfile.write('{}data->insert_1(current.values[0]);\n\n'.format(spaces_level_3))
                        
                elif (level == level_to_store_answer):
                    for view in predsToViewNames[variable_id]:
                        args = ', '.join('current.values[{}]'.format(x - 1) for
                                         x in viewNamesToCombinations[view])
                        
                        # If the identifier pertains to the solutions we have to append it as a solution
                        # to the database. Checking the getAllSolutions function to know what it is considered
                        # to be a solution will raise an error on the evaluation of some programs due to equal
                        # cards.
                        if variable_id in getPredicatesWithAllVariablesBeingInTheSharedSet() |\
                                          getPredicatesWithAllVariablesBeingInTheSharedSetIncludingConstants()|\
                                          getNegatedPredicates():
                            outfile.write('{}data->append_solution_{}({});\n'.format(spaces_level_3,
                                                                                     variable_id.name,
                                                                                     args))
                        
                        # We have to update the database if the identifier pertains to a variable
                        # that is going to be consulted in the database. That means it pertains to
                        # an equation  
                        if variable_id in getAllConsultingPredicates():
                            outfile.write('{}data->insert{}(Views::{}, {});\n'.format(spaces_level_3,
                                                                                      pred_length,
                                                                                      view,
                                                                                      args))
                    outfile.write('\n')
            
                    
            spaces = spaces_level_3
            for equation_number, equation in enumerate(equations, start=1):
                argument_constants_left_side = [ x for x in equation.leftArguments if x[0].type == 'constant']
                all_variables_same_equal_card = False
                
                if (equation_number > 1):
                    outfile.write('\n')
                
                if equation.type == 1:
                    # Do we have equal cards? If so we need to be sure they match before process the variable 
                    have_equal_cards = (len(set(equation.leftArguments)) != len(equation.leftArguments))
                    # Check if we have constant arguments (constants propagated trough the datalog source code)
                    if have_equal_cards:
                        temp_dict = defaultdict(list)
                        for rule_pos, (var_name, _) in enumerate(equation.leftArguments, 1):
                            temp_dict[var_name].append(rule_pos)
                            
                        lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                        
                        outfile.write('\n{}if ('.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            outfile.write('({})'.format(' == '.join( ['current.values[{}]'.format(x - 1) for x in l] )))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' &&\n{}    '.format(spaces))
                    if argument_constants_left_side:
                        if have_equal_cards:
                            outfile.write(' &&\n{}    '.format(spaces))
                        else:
                            outfile.write('{}if ('.format(spaces))
                            
                        for pos, elem in enumerate(argument_constants_left_side):
                            outfile.write('current.values[{}] == {}'.format(elem[1] - 1,
                                                                     str(elem[0].value)))
                            if pos != len(argument_constants_left_side)-1:
                                outfile.write(' &&\n{}    '.format(spaces))
                            
                    if have_equal_cards or argument_constants_left_side:
                        outfile.write(') {\n')
                        spaces += SPACES
                        
                    #new_var = 'var = new RewritingVariable(VariableType::{}, '.format(equation.rightVariable.id.name.upper())
                    args = [equation.rightVariable.id.name.upper()]
                    for pos, answer in enumerate(equation.rightArguments, 1):
                        # Check if we are dealing with a constant propagated trough the datalog source code.
                        # If we have an integer here it means it is a rewriting constant propagated value
                        # otherwise it is a constant specified on the datalog source code.
                        #new_var += compose_expression(answer, None, None)
                            
                        #if (pos != len(equation.rightArguments)): new_var += ", "
                        args.append(compose_expression(answer, None, None))
                        
                    #new_var += ')'
                    #outfile.write('{}{};\n'.format(spaces, new_var))
                        
                    common_block(spaces, equation, level, 
                                 len(GenerationData.stratums),
                                 args, idToStratumLevels)
                    
                    if have_equal_cards or argument_constants_left_side:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))        
                        
                if equation.type == 2:
                    commonVars_len = len(equation.commonVariables)
                    
                    argument_constants_consulting_values = [ x for x in equation.consultingArguments if
                                                               isinstance(x, Argument) and x.type == 'constant' ]
                    
                    # Manage the equal cards we have three cases. The equal cards can be in:
                    # The variable we are analyzing:
                    #    In this case we have to emit code to check that the corresponding variables, from
                    #    we already know the value as they come from the variable are equal. If they are
                    #    equal we can proceed otherwise we don't do anything.
                    # The consulting variables which are in the set of common variables:
                    #    In this case we have to emit code to handle properly the getint list value as we
                    #    have repeated values which come from the analyzing variable appearing may be only
                    #    one time
                    # The consulting variables which are not in the set of common variables
                    #    In this case we have to emit that the values we obtain iterating over the set
                    #    of common variables are equal otherwise as in the first case we would be adding
                    #    incorrect solutions
                    # Variables to control the different cases every name is self describing
                    # We transform a list into a set and check the lengths, if the lengths doesn't match
                    # we know that we have equal cards
                    equal_cards_rewriting_variable = (len(set(equation.leftArguments)) != len(equation.leftArguments))
                    # For the case of the set of common variables is a little bit more complex
                    equal_cards_query_common_vars = False
                    equal_cards_query_not_common_vars = False
                    # We proceed in the same way as before but now we use the consulting Values list
                    if (len(set(equation.consultingArguments)) != len(equation.consultingArguments)):
                        # We start extracting a list with the positions of the variables in the set of 
                        # common variables
                        common_var_positions = set(x[1] for x in equation.commonVariables)
                        # Next we obtain how many variables in the consulting values come with the rewriting 
                        # variable that is how many of the we now the position represented as an integer
                        number_of_common_vars = sum(1 for x in equation.consultingArguments if isinstance(x, int))
                        # Knowing the number of common variables we can split the list of consulting values
                        # and check for equal values in every part of the list. The first part is used to 
                        # check for if there are equal values in the set of common variables. The last part
                        # of the list is used to check if we have equal cards in the variables we have to 
                        # iterate to obtain new solutions. In this case we also have to check that there are
                        # more than one element otherwise the check for equal values using a set would give
                        # a false positive generating incorrect code
                        for x in equation.consultingArguments[:number_of_common_vars]:
                            if x in common_var_positions:
                                equal_cards_query_common_vars = True
                                break
                        # We are cheking for equal cards outside the set of common variables. We are only interested
                        # on the Arguments that are variables if it is a constant we have to discard it!!!!.
                        if (len(equation.consultingArguments[number_of_common_vars:]) > 1) and \
                           (len([x for x in equation.consultingArguments[number_of_common_vars:]
                                 if isinstance(x, Argument) and x.type == 'variable']) != \
                            len(set([x for x in equation.consultingArguments[number_of_common_vars:]
                                     if isinstance(x, Argument) and x.type == 'variable']))):
                                        equal_cards_query_not_common_vars = True
    
                    # If we have equal cards in the rewriting variable we are analyzing to emit code
                    # We have to check that the values represented by the equal cards are the same
                    if equal_cards_rewriting_variable:
                        # Here we create a dictionary in which every key is a variable name and its
                        # value is its relative position on the list. We have to do it in this way as the
                        # leftArguments represents a variable with a string and its position in the equation
                        # but if the variable is an equal card the position will be always the same, the 
                        # position of the first occurrence
                        temp_dict = defaultdict(list)
                        for rule_pos, (var_name, _) in enumerate(equation.leftArguments, 1):
                            temp_dict[var_name].append(rule_pos)
                                
                        # Once we have built the dictionary we create a list of lists removing the lists
                        # of length 1 as the represent the variables that are not equal cards
                        lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                            
                        # Once we have that lists of lists we only have to iterate through to emit the code
                        # Every list will contain the positions that should be equal. We emit an if in which
                        # every line are the positions of the list compared for equality and joined by logical 
                        # ands
                        outfile.write('{}if ('.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            outfile.write('({})'.format(' == '.join(['current.values[{}]'.format(x - 1) for x in l])))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' &&\n{}    '.format(spaces))
                        if argument_constants_left_side:
                            outfile.write(' &&\n{}    '.format(spaces))
                                                
                            for pos, elem in enumerate(argument_constants_left_side):
                                outfile.write('current.values[{}] == {}'.format(elem[1] - 1,
                                                                         str(elem[0].value)))
                                if pos != len(argument_constants_left_side)-1:
                                    outfile.write(' &&\n{}    '.format(spaces))
                                    
                        outfile.write(') {\n')
                        spaces += SPACES
                        
                        # Here we have to add the solution to the data structure if the predicate has all variables
                        # the same equal card. We check that if turning the list of leftArguments into a set the
                        # length is 1.
                        if len(set(equation.leftArguments)) == 1:
                            args = ['current.values[{}]'.format(x - 1) for x in l]
                            # TODO:
                            # This provokes on the parallel version of the evaluation to provide incorrect answers
                            # maybe should be removed from the sequential version too as may be it is not necessary
                            #outfile.write("{}if (data.check_and_update_solution_{}({})) {{\n".format(spaces,
                            #                                                                         equation.leftVariable.id.name,
                            #                                                                         ", ".join(args)))
                            #all_variables_same_equal_card = True
                            #spaces += SPACES
                    
                    elif argument_constants_left_side:
                        outfile.write('{}if ('.format(spaces))
                        
                        for pos, elem in enumerate(argument_constants_left_side):
                            outfile.write('current.values[{}] == {}'.format(elem[1] - 1,
                                                                            str(elem[0].value)))
                            if pos != len(argument_constants_left_side)-1:
                                outfile.write(' &&\n{}    '.format(spaces))
                                
                        outfile.write(') {\n')
                        spaces += SPACES
                        
                    
                    # Here we emit code to iterate over the necessary variables in order to get the desired 
                    # solutions, first we have to check if we are dealing with the case in which the set of
                    # common variables is empty. In that case we have to iterate over the level 0 of the
                    # data structure. This is not as efficient as it could as it will iterate over all the
                    # values stored at the level 0. Avoiding a case in which the root is node is different
                    # would solve this problem.
                    # If we have common variables then we have to check if we also have equal cards, in that
                    # case we have compute differently the number of common variables as the set of common 
                    # variables is actually a set and therefore doesn't accept duplicates.
                    # What we do is use the consulting values list which have the required duplicates.
                    # If we don't have equal cards in the set of common variables we just iterate over the
                    # list of common variables taking the position.
                    if commonVars_len == 0:
                        outfile.write('{}for (int t0: data->get_level0_values()) {{\n'.format(spaces))
                        spaces += SPACES
                        # If the length of the predicate is one we also have to make sure that the value we obtain
                        # is valid as we won't iterate to obtain more values
                        if len(equation.consultingArguments) == 1:
                            outfile.write('{}if (data->contains_solution_{}(t0))'.format(spaces,
                                                                                        equation.consultingPredicate.id.name))
                            outfile.write(' {\n')
                    
                    else:
                        # We don't have equal cards in the set of common variables, we just iterate over the set
                        # emitting code appropriately. 
                        if not equal_cards_query_common_vars:
                            args_common = ', '.join(['current.values[{}]'.format(x[1] - 1) for x in equation.commonVariables])
                            #int_length = commonVars_len + len(argument_constants_consulting_values)
                            int_length = commonVars_len + len(argument_constants_consulting_values)
                        # Here we have equal cards in the set of common variables there fore we need to check which is 
                        # the real number of common variables in the query.
                        else:
                            # The number of common variables is just the number of integer values of the consulting values
                            # list
                            number_of_common_vars = sum(1 for x in equation.consultingArguments if isinstance(x, int))
                                                     
                            args_common = ', '.join(['current.values[{}]'.format(x - 1)
                                                     for x in equation.consultingArguments[:number_of_common_vars]])
                                
                            #int_length = number_of_common_vars + len(argument_constants_consulting_values)
                            #commonVars_len = number_of_common_vars + len(argument_constants_consulting_values)
                            int_length = number_of_common_vars + len(argument_constants_consulting_values)
                            commonVars_len = number_of_common_vars
                        
                        if argument_constants_consulting_values:
                            args_common += ', ' + ', '.join(str(x.value) for x in argument_constants_consulting_values)
                         
                        # Here we have to check if the predicate we are consulting is the type that has all its variables
                        # the same equal card in that case we have to check against the solutions instead of iterating over
                        # the integer list of successors which doesn't make any sense as the predicate is true or false that means
                        # that contributes only with one solution or with none.
                        # If we turn the list of consulting values into a set and the length is 1 that means that the predicate
                        # has all its variables the same equal card
                        #if (len(set(equation.consultingArguments)) != 1 and\
                        #    getPredicateLength(equation.consultingPredicate.uniqueId) != len(equation.commonVariables)):
                        if (len(set([x for x in equation.consultingArguments if not (isinstance(x, Argument) and x.type=='constant')])) != 1 and\
                            getPredicateLength(equation.consultingPredicate.id) != len(equation.commonVariables) and 
                            sum([1 for x in equation.consultingArguments if isinstance(x, int) or (isinstance(x, Argument) and x.type=='constant')]) != len(equation.consultingArguments)):
                            # Here we just emit code for t1 using the computed values
                            outfile.write('{}l1 = data->get{}(Views::{}, {});\n'.format(spaces,
                                                                                        int_length + 1,
                                                                                        aliasToViewNames[equation.aliasName],
                                                                                        args_common))
                            outfile.write('{}l1->lock();\n'.format(spaces))
                            if set(filter(lambda x: isinstance(x, Argument), 
                                          equation.rightArguments)).intersection(filter(lambda x: isinstance(x, Argument), 
                                                                                        equation.consultingArguments)) or len(equation.consultingArguments) > 1:
                                outfile.write('{}for (int t1: *l1->get_array()) {{\n'.format(spaces))
                            else:
                                outfile.write('{}if (!l1->get_array()->empty()) {{\n'.format(spaces))
                        else:
                            all_variables_same_equal_card = True
                            outfile.write("{}if (data->contains_solution_{}({})) {{\n".format(spaces,
                                                                                             equation.consultingPredicate.id.name,
                                                                                             args_common))
                            #spaces += SPACES
    
                    # Here we emit code for the rest of the required t levels that value is the number
                    # of consulting values minus the number of common variables which has already been
                    # used in the t1 level
                    start = 2
                    if commonVars_len == 0:
                        start = 1
                    for (x, y) in enumerate(xrange(commonVars_len + 1, 
                                                   len(equation.consultingArguments) - len(argument_constants_consulting_values)),
                                            start=start):
                        #spaces = spaces + (SPACES * (x - 1))
                        if x > 1: spaces += SPACES
                        query_value = y + len(argument_constants_consulting_values)
                        if commonVars_len == 0:
                            args = 't0'
                            if x > 1: args += ', '
                        else:
                            args = args_common + ', '
                           
                        if not equal_cards_query_common_vars:
                            args += ', '.join(['t{}'.format(i) for i in xrange(1, x)])
                            outfile.write('{}l{} = data->get{}(Views::{}, {});\n'.format(spaces,
                                                                                         x,
                                                                                         query_value + 1,
                                                                                         aliasToViewNames[equation.aliasName],
                                                                                         args))
                            outfile.write('{}l{}->lock();\n'.format(spaces, x))
                            outfile.write('{}for (int t{}: *l{}->get_array())'.format(spaces, x, x))
                        else:
                            args += ', '.join(['t{}'.format(i) for i in xrange(1, (y-commonVars_len)+1)])
                            outfile.write('{}l{} = data->get{}(Views::{}, {});\n'.format(spaces,
                                                                                         (y-commonVars_len) + 1,
                                                                                         query_value + 1,
                                                                                         aliasToViewNames[equation.aliasName],
                                                                                         args))
                            outfile.write('{}l{}->lock();\n'.format(spaces, (y-commonVars_len) + 1))
                            outfile.write('{}for (int t{}: *l{}->get_array())'.format(spaces,
                                                                                      (y-commonVars_len) + 1,
                                                                                      (y-commonVars_len) + 1))

                                          
                        outfile.write(' {\n')
                    
                    spaces += SPACES
                    
                    # Here we handle if we have equal cards in the query variables that are
                    # not in the set of common variables. As we retrieve them from the iterating
                    # lists we have to check that are equal otherwise we would count
                    # invalid answers not honoring the equal cards. To do so we have to check
                    # which of the variables not in the set of the common variables are repeated
                    if equal_cards_query_not_common_vars:
                        if len(set(equation.consultingArguments)) != 1:
                            # The key of the dict will be the name of the variable.
                            # The value of the dict will be a list containing the positions in which
                            # the variable appears repeated
                            temp_dict = defaultdict(list)
                            # Here we compute the first occurrence of the variables.
                            # We compute where the first string appears in the list.
                            number_of_common_vars = sum(1 for x in equation.consultingArguments if isinstance(x, int))
                            # Here we iterate over the list of variables that are not in the set of common variables. The
                            # variables start after the variables that belong to the set of common variables and are represented 
                            # by its string name. We have to subtract the number of common variables as the first iterating variable
                            # is always t1 and not t? being ? the position its the list of consultingArguments
                            for rule_pos, var_name in enumerate(equation.consultingArguments[number_of_common_vars:], number_of_common_vars+1):
                                temp_dict[var_name].append(rule_pos - number_of_common_vars - len(argument_constants_consulting_values))
                                  
                            # Here we create a lists of lists removing the lists of only one member as that implies 
                            # that is not a duplicated variable. Every list will contain the position of the duplicated 
                            # variables
                            lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                        else:
                            lists_of_duplicated_vars = [list(xrange(len(equation.consultingArguments)))]
                            
                        # We only have to iterate over each list emitting code appropriately 
                        outfile.write('{}if ('.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            t = ['t{}'.format(x) for x in l]
                            outfile.write('{}'.format(' == '.join(t)))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' &&\n{}    '.format(spaces))
                        outfile.write(') {\n')
                        spaces += SPACES
                        
                    #outfile.write('{}var = new RewritingVariable(VariableType::{}'.format(spaces,
                    #                                                                     equation.rightVariable.id.name.upper()))
                    
                    args = [equation.rightVariable.id.name.upper()]
                    # Here we emit code to create the new variable. We start iterating
                    # from the rightArguments and check for every variable position of the
                    # answer which other variable goes if it is a variable name we check
                    # which of the "t" values is required. The "t" values are used to 
                    # iterate over the set of common vars. If is just a number it means
                    # it comes from the variable so we just to use that value. We also have
                    # to handle the case in which there are no common variables for that case
                    # we start at t0 as we have to iterate over all the variables of the other
                    # predicate.
                    for pos, var in enumerate(equation.rightArguments, start=1):
                        code = compose_expression(var,
                                                  equation.consultingArguments,
                                                  equation.commonVariables)
                        #outfile.write(", {}".format(code))
                        args.append(code)

                    #outfile.write(');\n')
                    
                    #common_block(spaces, equation, level,
                    #             len(GenerationData.stratums),
                    #             idToStratumLevels)
                    common_block(spaces, equation, level,
                                 len(GenerationData.stratums),
                                 args, idToStratumLevels)
                    
                    # Here we just emit source code to handle the indentation and the close every 
                    # required '}' character                    
                    if equal_cards_query_not_common_vars:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))
                    
                    for x in xrange(len(equation.consultingArguments) - len(argument_constants_consulting_values), commonVars_len, -1):
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))
                        if commonVars_len == 0:
                            if (x - 1 > 0):
                                outfile.write('{}l{}->unlock();\n'.format(spaces,
                                                                         x - 1))
                        else:
                            outfile.write('{}l{}->unlock();\n'.format(spaces,
                                                                     x - commonVars_len))
                    
                    if equal_cards_rewriting_variable or argument_constants_left_side:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))
                    
                    if all_variables_same_equal_card:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))
                        
                    if commonVars_len == 0 and len(equation.consultingArguments) == 1:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))

            spaces = spaces[:-len(SPACES)]
            outfile.write('{}}}\n'.format(spaces))
            
        # THIS HAS TO BE PRINTED IF WE WORK WITH THE SOLVER QUEUE BASED IN ONE QUEUE
        #outfile.write('{0}solver_queue{1}.head = solver_queue{1}.head->next;\n'.format(spaces_level_2,
        #                                                                               str(level)))
        outfile.write('{}}}\n'.format(spaces_level_1))
        
        # Close the files of the answers in case we have to
        if answerFileNames:
            outfile.write('{}// Close the output file streams\n'.format(SPACES))
            outfile.write('\n'.join('{}{}.close();'.format(SPACES, x) for x in answerFileNames))
            outfile.write('\n')
        
        # End the function
        outfile.write('}\n\n')
        
             

fill_template = {
    'fillRewritingVariable':  fillRewritingVariable,
    'fillViews':  fillViews,
    'fillVariableType' : fillVariableType,
    'fillDatastructureCreateNodeStructs' : fillDataStructureCreateNodeStructs,
    'fillDatastructureRootData' : fillDataStructureRootData,
    'fillDatastructureHeaders' : fillDataStructureHeaders,
    'fillDatastructureInsertFunctions' : fillDataStructureInsertFunctions,
    'fillDatastructureGetLevel0Values' : fillDataStructureGetLevel0Values,
    'fillDatastructureGetFunctions' : fillDataStructureGetFunctions,
    'fillDatastructureContainsSolutionFunctions' : fillDataStructureContainsSolutionFunctions,
    'fillDatastructureAppendSolutionFunctions': fillDataStructureAppendSolutionFunctions, 
    'fillDatastructureCheckAndUpdateFunctions' : fillDataStructureCheckAndUpdateFunctions,
    'fillSolverPrivateDataAndFunctions' : fillSolverPrivateDataAndFunctions,
    'fillSolverWriteRewritingVariable' : fillSolverWriteRewritingVariable,
    'fillSolverInitFunction' : fillSolverInitFunction,
    'fillSolverEndFunction' : fillSolverEndFunction,
    'fillSolverComputeFunction' : fillSolverComputeFunction,
    'fillSolverInitStratumFunctions' : fillSolverInitStratumFunctions,
    'fillSolverComputeStratumClasses' : fillSolverComputeStratumClasses
     }

def fill_file(filename, orig_file, dest_file):
    with open(orig_file, 'r') as infile:
        with open(dest_file, 'w') as outfile:
            # Check if the first line calls fill_Header
            line = infile.readline()
            if line.split()[1] == 'fill_Header':
                header =  '/**\n * {}\n'.format(filename)
                header += ' * Created by: {}\n'.format('CPP Code Generator')
                header += ' * Created on: {}\n'.format(datetime.today().date())
                header += ' */\n'
            else:
                header = line
            
            outfile.write(header)

            for line, line_number in zip(infile, count(2)):
                if line.startswith(DELIMITER):
                    function = line.split()[1]
                    try:
                        fill_template[function](outfile)
                    except KeyError as e:
                        print e
                        print "Error: {}: {}: Unknown directive: {}".format(filename,
                                                                            line_number,
                                                                            function)
                        sys.exit(-1)
                else:
                    outfile.write(line)
                    
    return True

# Options for the module:
#  Backend, Queue
#
# Backend -> It represents the static data is implemented
# The possible options are:
#     Native -> It will use a pure python representation of the data structure e
#     SQLite -> It will use the SQLite module from the standard library
# Queue -> It represents how the dynamic queue is implemented
# The possible options are:
#     Deque -> A python deque (from the standard library).
#     Redis -> To use redis key-store database (python-redis must be installed and 
#                                               a redis server must be running on 
#                                               the local machine).
def generate_code_from_template(output_directory, stratums, 
                                predicateTypes, answersToStore,
                                printVariables, idToStratumLevels):
    # Make the necessary data to generate the source code available to the rest of the functions
    GD = namedtuple('GD', ['stratums', 'predicateTypes', 'answersToStore', 
                           'printVariables', 'idToStratumLevels'])
    
    globals()['GenerationData'] = GD(stratums, predicateTypes,
                                     answersToStore, printVariables,
                                     idToStratumLevels)
    
    #Check that the output directory exists
    path = os.path.normpath(output_directory + '/Solver_CPP_code')
    include_path = os.path.normpath(path + '/include')
    libcuckoo_path = os.path.normpath(include_path + '/libcuckoo')
    if os.path.exists(path):
        shutil.rmtree(path)
    
    os.makedirs(path)
    os.makedirs(include_path)
    
    
    # Manage the libcuckoo header files
    cuckoo_orig_path = os.path.normpath(SOURCE_DIRECTORY + "/include/libcuckoo/")
    cuckoo_dest_path = os.path.normpath(libcuckoo_path + "/")
    shutil.copytree(cuckoo_orig_path, cuckoo_dest_path)
        
    # Manage the header files
    for header_file in INCLUDE_FILES:
        orig_path = os.path.normpath(SOURCE_DIRECTORY + "/include/" + header_file)
        dest_path = os.path.normpath(include_path + "/" + header_file)
        fill_file(header_file, orig_path, dest_path)
        
    # Manage the source files
    for source_file in SOURCE_FILES:
        orig_path = os.path.normpath(SOURCE_DIRECTORY + "/" + source_file)
        dest_path = os.path.normpath(path + "/" + source_file)
        fill_file(source_file, orig_path, dest_path)