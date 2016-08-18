'''
Created on Dec 3, 2015

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


# Settings for the parser
DELIMITER = '%%'
SOURCE_DIRECTORY = "Py_Template"
#OUTPUT_DIRECTORY = "./"

SOURCE_FILES = ['datastructure.py', 'utils.py', 'main.py', 'solver.py']

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

def print_append_query_to_the_trie(outfile, length, spaces):
    for x in xrange(1, length):
        query = ''
        for y in xrange(1, x):
            query += '[x_{}][0]'.format(y)
        outfile.write('{0}if not self.__root{1}.has_key(x_{2}):\n'.format(spaces,
                                                                          query,
                                                                          x))
        if x == 1:
            query = '[x_1]'
        else:
            query += '[x_{}]'.format(x)
        outfile.write('{0}self.__root{1} = self.__create_node{2}()\n'.format(spaces + SPACES,
                                                                             query,
                                                                             x + 1))

def fillSolutions(outfile):
    c = Counter()
    viewsData = []
    
    last_level_of_the_data_structure = getDataStructureNodesMaximumLength()
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    viewLengths = list((len(x) for x in viewNamesToCombinations.itervalues()))
    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    
    lengths = list(xrange(2, number_of_data_structure_nodes+1))
    for length in lengths:
        viewsData.append((length, viewLengths.count(length)))
        
    outfile.write('# Solution position values\n')
    for variable_id in getAllSolutions():
        count = 0
        
        length = getPredicateLength(variable_id)
        position = c[length]
        number_of_views_for_this_level = sum((x[1]) for x in viewsData 
                                             if x[0] >= length)

        if length != last_level_of_the_data_structure:
            count = 1

        outfile.write('solution_{} = {}\n'.format(variable_id.name, position + number_of_views_for_this_level + count))
        c[length] += 1

def fillAccessViews(outfile):
    #sorted_views = GenerationData.viewsData.viewsOrdering
    sorted_views = [ view.viewsOrdering for view in getViewsFromAllStratums() ]
    
    view_names = []
    views_values = []
    for view_name, view_position in chain(*sorted_views):
        view_names.append(view_name)
        views_values.append("{}={}".format(view_name,
                                           view_position))
        
    outfile.write('# Views\n')
    outfile.write("Views = namedtuple('Views', [{}], verbose=False)\n".format(", ".join(map(lambda x: "'" + x + "'",
                                                                                            view_names))))
    outfile.write('views = Views({})\n'.format(', '.join(views_values)))
    
def fillHypothesesNames(outfile):
    hypotheses = set(eq.leftVariable.id.name for eq in getEquationsFromAllStratums())
    hypotheses |= set(eq.rightVariable.id.name for eq in getEquationsFromAllStratums())
    hypotheses |= set(negated_element.id.name 
                            for eq in getEquationsFromAllStratums()
                            for negated_element in eq.negatedElements)
    outfile.write('# Hypotheses\n')
    outfile.write("Hypotheses = namedtuple('Hypotheses', [{}], verbose=False)\n".format(", ".join(map(lambda x: "'" + x + "'",
                                                                                                      hypotheses))))
    outfile.write('hypotheses = Hypotheses({})'.format(', '.join(map(str, xrange(len(hypotheses))))))

def fillInitDataStructure(outfile):
    spaces_for_function_definition = SPACES
    spaces_for_function_body = SPACES * 2
    
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
    
    outfile.write('{}def __init__(self):\n'.format(spaces_for_function_definition))
    outfile.write('{}self.__root = dict()\n'.format(spaces_for_function_body))
    
    for variable_id in answers_of_length_1.union(predicates_in_rules_of_length_1):
        outfile.write('{}self.R_{} = set()\n'.format(spaces_for_function_body,
                                               variable_id.name))

def fillCreateNodes(outfile):
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    
    try:
        max_query_length = getQueryMaximumLength()
    except ValueError:
        max_query_length = 0
        
    max_data_structure_length = max(max(x[1] for x in getAllPredicatesLengths() if x[0] in getAllSolutions()),
                                    max_query_length)
        
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
            
    
    viewsData = []
    viewLengths = list((len(x) for x in viewNamesToCombinations.itervalues()))
    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    
    lengths = list(xrange(2, number_of_data_structure_nodes+1))
    for length in lengths:
        viewsData.append((length, viewLengths.count(length)))

    spaces_for_function_definition = SPACES
    spaces_for_function_body = SPACES * 2
    for length in lengths:
        line_body = ''
        # Are we in the last level?
        # Otherwise we need a link to the next level. This is represented as a dict 
        if length != number_of_data_structure_nodes:
            line_body = 'dict(), '
            
        # How many views do we have at this level
        number_of_views_for_this_level = sum((x[1]) for x in viewsData 
                                             if x[0] >= length)
        # How many solutions do we have on the level. Solutions are represented as sets
        number_of_solutions_for_this_level = sum(1 for variable_id in lengthToPreds[length]
                                                        if variable_id in getAllSolutions())
        
        line_body += ", ".join(repeat("array('L')", number_of_views_for_this_level))
        
        #if number_of_views_for_this_level >= 1 and\
        #   number_of_solutions_for_this_level > 0 and\
        #   length == max_data_structure_length:
        #    line_body += ','
        if (number_of_views_for_this_level >= 1 and number_of_solutions_for_this_level >= 1) or\
            (number_of_views_for_this_level == 1 and number_of_solutions_for_this_level == 0 and\
             length == max_data_structure_length):
            line_body += ', '
        
        if number_of_solutions_for_this_level:
            #if length < max_data_structure_length or length <= max_query_length:
            #    line_body += ", "
            if number_of_views_for_this_level == 0 and\
                length < max_data_structure_length:
                line_body += ', '

            line_body += ", ".join(repeat('set()', 
                                          number_of_solutions_for_this_level))
            if length == max_data_structure_length and number_of_solutions_for_this_level == 1 and\
                number_of_views_for_this_level == 0:
                line_body += ", "

        line_body = 'return (' + line_body + ')'
        line = '{}def __create_node{}(self):\n{}{}\n'.format(spaces_for_function_definition,
                                                             length,
                                                             spaces_for_function_body,
                                                             line_body)
        outfile.write(line)
        outfile.write(EMPTY_LINE)

@check_for_predicates_of_type2
def fillInsertNodes(outfile):
    def print_code_for_Ds_insert_1():
        spaces_level1 = SPACES
        spaces_level2 = SPACES * 2
        spaces_level3 = SPACES * 3
        outfile.write('{}def insert1(self, x_1):\n'.format(spaces_level1))
        outfile.write('{}if x_1 not in self.__root:\n'.format(spaces_level2))
        if getDataStructureNodesMaximumLength() > 1:
            outfile.write('{}self.__root[x_1] = self.__create_node2()\n'.format(spaces_level3))
        else:
            outfile.write('{}self.__root[x_1] = tuple()\n'.format(spaces_level3))
        outfile.write(EMPTY_LINE)
        
        
    lengths = xrange(getQueryMinimumLength(), getQueryMaximumLength()+1)
    last_level_of_the_data_structure = getDataStructureNodesMaximumLength()
    
    spaces_for_function_definition = SPACES
    spaces_for_function_body = SPACES * 2
    for length in lengths:
        # We have to handle length 1 differently. If we detect that the current length is 1 as we don't
        # have a level 1 node for the data structure we have to emit code differently that is why the
        # auxiliary function code_for_Ds_insert_1 is invoked and then we continue the to the next length.
        # We do it in this way as is easier to create an auxiliary function for this case that to add
        # checks for the control flow to detect if we are in the length 1 case every time we emit code.
        if length == 1:
            print_code_for_Ds_insert_1()
            continue
        
        args_to_function = ('x_{}'.format(str(v+1)) for v in xrange(length))
        outfile.write('{}def insert{}(self, pos, {}):\n'.format(spaces_for_function_definition,
                                                                length,
                                                                ", ".join(args_to_function)))
        
        # Check key and if it doesn't exist create a node
        print_append_query_to_the_trie(outfile, length, spaces_for_function_body)
        
        outfile.write(EMPTY_LINE)
        for x in xrange(1, length):
            pos = 'pos'
            if (x + 1) != last_level_of_the_data_structure:
                pos += '+1'
                
            query = '[x_1]'
            for y in xrange(1, x):
                query += '[0][x_{}]'.format(y+1)
            outfile.write('{0}self.__root{1}[{2}].append(x_{3})\n'.format(spaces_for_function_body,
                                                                          query,
                                                                          pos,
                                                                          x + 1))
        outfile.write(EMPTY_LINE)
    
def fillGetLevel0Values(outfile):
    spaces_for_function_definition = SPACES
    spaces_for_function_body = SPACES * 2
    
    outfile.write('{}def get_level0_values(self):\n'.format(spaces_for_function_definition))
    outfile.write('{}return self.__root.iterkeys()\n'.format(spaces_for_function_body))
    outfile.write(EMPTY_LINE)

@check_for_predicates_of_type2
def fillGetFunctions(outfile):
    lengths = xrange(2, getQueryMaximumLength()+1)
    last_level_of_the_data_structure = getDataStructureNodesMaximumLength()
    
    spaces_for_function_definition = SPACES
    spaces_for_function_body = SPACES * 2
    for length in lengths:
        args_to_function = ('x_{}'.format(str(v+1)) for v in xrange(length - 1))
        outfile.write('{}def get{}(self, pos, {}):\n'.format(spaces_for_function_definition,
                                                             length,
                                                             ", ".join(args_to_function)))
        
        outfile.write('{0}if '.format(spaces_for_function_body))
        for x in xrange(1, length):
            query = ''
            for y in xrange(1, x):
                query += '[x_{}][0]'.format(y)
            outfile.write('self.__root{}.has_key(x_{})'.format(query,
                                                                  x))
            if (x != length - 1):
                outfile.write(' and\\\n{}   '.format(spaces_for_function_body))
        outfile.write(':\n')
        
        pos = 'pos'
        if (x + 1) != last_level_of_the_data_structure:
            pos += '+1'
            
        query = '[x_1]'
        for x in xrange(1, length-1):
            query += '[0][x_{}]'.format(x+1)
        outfile.write('{0}return self.__root{1}[{2}]\n'.format(spaces_for_function_body + SPACES,
                                                               query,
                                                               pos))

        outfile.write('\n{}return list()\n'.format(spaces_for_function_body))
        outfile.write(EMPTY_LINE)
        
def fillAppendFunctions(outfile):
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    
    for variable_id in getAllSolutions():
        length = getPredicateLength(variable_id)
        args = ('x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('{}def append_solution_{}(self, {}):\n'.format(spaces_level_1,
                                                                     variable_id.name,
                                                                     ', '.join(args)))
        
        if length == 1:
            outfile.write('{}self.R_{}.add(x_1)\n'.format(spaces_level_2,
                                                                 variable_id.name))
            continue
        
        
        # Check key and if it doesn't exist create a node
        print_append_query_to_the_trie(outfile, length, spaces_level_2)
        
        outfile.write(EMPTY_LINE)
        query = '[x_1]'
        for x in xrange(1, length-1):
            query += '[0][x_{}]'.format(x+1)
            
        outfile.write('{0}self.__root{1}[solution_{2}].add(x_{3})\n'.format(spaces_level_2,
                                                                            query,
                                                                            variable_id.name,
                                                                            length))

        outfile.write(EMPTY_LINE)
        
def fillContainsFunctions(outfile):
    spaces_for_function_definition = SPACES
    spaces_for_function_body = SPACES * 2
    for variable_id in getAllSolutions():
        length = getPredicateLength(variable_id)
        args = ('x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('{}def contains_solution_{}(self, {}):\n'.format(spaces_for_function_definition,
                                                                      variable_id.name,
                                                                      ', '.join(args)))
        
        if length == 1:
            outfile.write('{}return (x_1 in self.R_{})\n'.format(spaces_for_function_body,
                                                                 variable_id.name))
            continue
        
        
        for x in xrange(1, length):
            query = ''
            for y in xrange(1, x):
                query += '[x_{}][0]'.format(y)
            outfile.write('{0}if not self.__root{1}.has_key(x_{2}):\n'.format(spaces_for_function_body,
                                                                              query,
                                                                              x))
            outfile.write("{0}return False\n".format(spaces_for_function_body + SPACES))
            
        query = '[x_1]'
        for x in xrange(1, length-1):
            query += '[0][x_{}]'.format(x+1)
            
        outfile.write(EMPTY_LINE)
        outfile.write('{}return (x_{} in self.__root{}[solution_{}])\n'.format(spaces_for_function_body,
                                                                               length,
                                                                               query,
                                                                               variable_id.name))
            
        outfile.write(EMPTY_LINE)

def fillPrintAnswer(outfile):
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    
    outfile.write('def print_answer(f, var):\n')
    for position, ((pred_name, _), length) in enumerate(getAllPredicatesLengths()):
        if position == 0:
            conditional = 'if'
        else:
            conditional = 'elif'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['var[{}]'.format(x) for x in xrange(1, length+1)])
        
        outfile.write('{}{} (var[0] == hypotheses.{}):\n'.format(spaces_level_1,
                                                                 conditional, 
                                                                 pred_name))

        outfile.write('{}f.write("{}({}).\\n" % ({}))\n'.format(spaces_level_2,
                                                                pred_name,
                                                                formatting,
                                                                variables))
        
def fillPrintRewritingVariable(outfile):
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    
    outfile.write('def print_rewriting_variable(var):\n')
    for position, ((pred_name, _), length) in enumerate(getAllPredicatesLengths()):
        if position == 0:
            conditional = 'if'
        else:
            conditional = 'elif'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['var[{}]'.format(x) for x in xrange(1, length+1)])
        
        outfile.write('{}{} (var[0] == hypotheses.{}):\n'.format(spaces_level_1,
                                                                 conditional, 
                                                                 pred_name))

        outfile.write('{}print "{}({})." % ({})\n'.format(spaces_level_2,
                                                          pred_name,
                                                          formatting,
                                                          variables))

def fillStrtatumSolverQueues(outfile):
    number_of_stratums = len(GenerationData.stratums)
    queues = "\n".join('solver_queue' + str(x) + ' = deque()' for x in xrange(1, number_of_stratums+1))
    outfile.write('{}'.format(queues))
    outfile.write(EMPTY_LINE)
    
def fillStratumQueueInitializers(outfile):
    extensional = list(getExtensionalPredicates())
    extensional_as_set = set(extensional)
    idToStratumLevels = GenerationData.idToStratumLevels
    number_of_stratums = len(GenerationData.stratums)
    
    # Create a new dictionary from idToStratumLevels only containing
    # extensional predicates
    extensionalToStratumLevels = {k: v for (k,v) in idToStratumLevels.iteritems() if k in extensional_as_set}
    
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    for stratum_level in xrange(1, number_of_stratums + 1):
        outfile.write('def solver_init_stratum_level{}():\n'.format(str(stratum_level)))
        
        if DEBUG:
            outfile.write('{}print "STRATUM LEVEL: {}\\n"\n\n'.format(spaces_level_1,
                                                                      str(stratum_level)))
        
        # Get the predicates that belong to the current stratum level
        idsVars = (idVar for (idVar, levels) in extensionalToStratumLevels.iteritems()
                                if stratum_level in levels)
        
        # If we are in the first of the level we must honor the order of the block
        # as negated predicates must be put first
        if (stratum_level == 1):
            idsVarsSet = set(idsVars)
            idsVars = ( x for x in extensional if x in idsVarsSet )
            
        for idVar in idsVars:
            outfile.write("{}fp = open('{}.tuples')\n".format(spaces_level_1,
                                                              idVar.name))
            outfile.write("{}for l in fp.readlines():\n".format(spaces_level_1))
            outfile.write("{}values = map(int, l.strip()[:-2].split('(')[1].split(','))\n".format(spaces_level_2))
            outfile.write('{}solver_queue{}.append(([hypotheses.{}] + values))\n'.format(spaces_level_2,
                                                                                         stratum_level,
                                                                                         idVar.name))
            outfile.write('{}fp.close()\n'.format(spaces_level_1))
            outfile.write(EMPTY_LINE)
    
def fillSolverInit(outfile):
    spaces_level_1 = SPACES
    outputTuples = GenerationData.answersToStore
    
    outfile.write(' = '.join('fp_{}'.format(ident.name) for ident in outputTuples))
    outfile.write(' = None\n')
    outfile.write('def solver_init():\n')
    outfile.write('{}global {}\n'.format(spaces_level_1,
                                       ', '.join('fp_{}'.format(ident.name) for ident in outputTuples)))
    for ident in outputTuples:
        outfile.write('{0}fp_{1} = open("{1}.tuples", "w+")\n'.format(spaces_level_1,
                                                                      ident.name))

    outfile.write(EMPTY_LINE)
            
def fillSolverCompute(outfile):
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
            return "current[{}]".format(expression)
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
                    emitting_code += "current[{}]".format(args[x])
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
    def common_block(spaces, equation, level, num_of_stratums, idToStratumLevels):
        # Do we have to store the answer??
        if equation.rightVariable.id in answersToStore:
            variable_id = equation.rightVariable.id

            args = ', '.join('var[{}]'.format(x) for 
                            x in xrange(1, len(equation.rightArguments)+1))
            
            outfile.write('\n{}if not data.contains_solution_{}({})'.format(spaces,
                                                                            variable_id.name,
                                                                            args))
            
            if equation.booleanExpressions:
                outfile.write( ' and\\\n{0}{1}'.format(spaces,
                                                       '    '))
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
                        boolean_expressions_str += " and\\\n{}{}".format(spaces,
                                                                         '    ')
                        
                outfile.write(boolean_expressions_str)
            
            if equation.negatedElements:
                outfile.write( ' and\\\n')
            
            for (pos, negated_element) in enumerate(equation.negatedElements):
                negated_arguments_str = []

                for negated_arg in negated_element.arguments:
                    if negated_arg.type == 'constant':
                        negated_arguments_str.append(str(negated_arg.value))
                    else:
                        found = False
                        for argument, position in equation.leftArguments:
                            if negated_arg == argument:
                                negated_arguments_str.append('current[{}]'.format(position))
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
                
                negated_arguments = ', '.join(negated_arguments_str)
                outfile.write('{}{}not data.contains_solution_{}({})'.format(spaces,
                                                                             '    ',
                                                                             negated_element.id.name,
                                                                             negated_arguments))
                if (pos != len(equation.negatedElements) - 1):
                    outfile.write(' and\\\n')
            spaces += SPACES
            outfile.write(':\n')
            if DEBUG:
                # Print the variable information
                outfile.write('{}print "\\tAdding variable -> ",\n'.format(spaces))
                outfile.write('{}print_rewriting_variable(var)\n'.format(spaces))
                # Print the levels in which the variable is going to be added. Here is printed for
                # debugging purposes.
                for level in idToStratumLevels[variable_id]:
                    outfile.write('{}print "\\t  Queue {}"\n'.format(spaces, str(level)))

            
            # To compute a program a variable can be required to be evaluated in different queues, here we
            # make sure that the variable is added to every required queue. IdToStratums is a dictionary that
            # contains the required information to emit the code. It takes as a key a variable_id and returns
            # the queue levels in which is required.
            for queue_level in idToStratumLevels[variable_id]:
                outfile.write('{}solver_queue{}.append(var)\n'.format(spaces, str(queue_level)))
                
            outfile.write('{}data.append_solution_{}({})\n'.format(spaces,
                                                                    variable_id.name,
                                                                    args))
        else:
            outfile.write('{}solver_queue1.append(var)\n'.format(spaces))
            
    predsToViewNames = dict(chain(*[ view.predsToViewNames.items() for view in getViewsFromAllStratums() ]))
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    aliasToViewNames = dict(chain(*[ view.aliasToViewNames.items() for view in getViewsFromAllStratums() ]))
    answersToStore = GenerationData.answersToStore
    printVariables = GenerationData.printVariables
    outputTuples = GenerationData.answersToStore
    idToStratumLevels = GenerationData.idToStratumLevels
    
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    spaces_level_3 = SPACES * 3
    
    outfile.write('def solver_compute():\n')
    outfile.write('{}data = datastructure()\n'.format(spaces_level_1))
    outfile.write('{}var = None\n\n'.format(spaces_level_1))
    # Here we emit code to handle the different stratums in the solver_compute function
    for level, stratum in enumerate(GenerationData.stratums, start=1):
        outfile.write('{}#* Stratum {} *#\n'.format(spaces_level_1, 
                                                level))
        outfile.write('{}solver_init_stratum_level{}()\n'.format(spaces_level_1,
                                                                  level))
        outfile.write('{}while (solver_queue{}):\n'.format(spaces_level_1,
                                                           level))
        outfile.write('{}current = solver_queue{}.popleft()\n\n'.format(spaces_level_2,
                                                                     level))
        
        block1 = stratum.ordering.block1
        block2 = stratum.ordering.block2
        block3 = stratum.ordering.block3
    
        for variable_id in chain(block1, block2, block3):
            # Get the equation of the predicate raise an exception if not found
            equations = (x for x in getEquationsFromAllStratums() if x.leftVariable.id == variable_id)
    
            outfile.write('{}if current[0] == hypotheses.{}:\n'.format(spaces_level_2,
                                                                       variable_id.name))

            # The answer can be represented in more than one level (stratum). We need to 
            # assure that we only emit the answer once, otherwise the solution would appear 
            # as many times as it appears in the different level. In which level we store
            # the answer is meaningless but we have to make sure that we only do it once,
            # so we store in the first stratum the answer appears represented. To do this
            # we sort the levels the in which the variable appears take the first one and
            # check that is the level that the code is being emitted. 
            level_to_store_answer = sorted(idToStratumLevels[variable_id])[0]
            # Do we have to print the variable to stdout?.
            if level == level_to_store_answer and variable_id in printVariables:
                outfile.write("{}print_rewriting_variable(current)\n".format(spaces_level_3))
                
            # Is it a solution? Then print it to a file.
            if level == level_to_store_answer and variable_id in outputTuples:
                outfile.write("{}print_answer(fp_{}, current)\n".format(spaces_level_3,
                                                                        variable_id.name))
            
            pred_length = getPredicateLength(variable_id)
            # Debug information
            if DEBUG:
                outfile.write('{}print "Handling rewriting variable X_{}({})" % ({})\n'.format(spaces_level_3,
                                                                                               variable_id.name,
                                                                                               ', '.join('%i' for _ in xrange(pred_length)),
                                                                                               ', '.join('current[{}]'.format(x) for x in xrange(1, pred_length+1))))
                              
            # Here we emit code to add data to the data structure if we are in a type 2 equation.
            # Again we only store the variable to the database if we are in the first level (stratum)
            # the variable appears in.
            # We emit debugging code via a c macro to check what is going to be added
            # to the data structure. We show the view and the values being added.
            # After we use the appropriate call to add the solution to the data structure
            if variable_id in predsToViewNames:
                  
                # Debug information: If the predicate has length 1 the it becomes a solution and has to be
                # treated as such. Otherwise we insert a value into the list as normal
                if DEBUG:
                    if (level == level_to_store_answer) and (pred_length == 1):
                        outfile.write('{}print "Data structure: Adding solution {}("'.format(spaces_level_3,
                                                                                             variable_id.name))
                        outfile.write(' + ", ".join(current[1:]) + ")"\n')
                    elif (level == level_to_store_answer):
                        for view in predsToViewNames[variable_id]:
                            args = ', '.join('current[{}]'.format(x) for
                                             x in viewNamesToCombinations[view])
                            formatting = ', '.join(('%i' for _ in viewNamesToCombinations[view]))
                            outfile.write('{}print "\\tData structure: Adding {}({})" % ({})\n'.format(spaces_level_3,
                                                                                                       view,
                                                                                                       formatting,
                                                                                                       args))
                  
            
            # Unfortunately because of the problem of the previous line we have to recheck here if the
            # predicate has a view associated with it
            if variable_id in predsToViewNames:     
                # This is part in which we add the solution to the data structure. If the predicate has length
                # 1 we have to add directly the solution, as by convention there is no level node of length 0
                # and the predicates of length 1 are turned into solutions
                if (level == level_to_store_answer) and (pred_length == 1):
                    outfile.write('{}data.append_solution_{}(current[1])\n'.format(spaces_level_3,
                                                                                   variable_id.name))
                    # If the variable only appears as a negated predicate we don't have to insert it to the database
                    if variable_id in getAllConsultingPredicates():
                        outfile.write('{}data.insert1(current[1])\n\n'.format(spaces_level_3))
                elif (level == level_to_store_answer):
                    for view in predsToViewNames[variable_id]:
                        args = ', '.join('current[{}]'.format(x) for
                                            x in viewNamesToCombinations[view])
                        
                        # If the identifier pertains to the solutions we have to append it as a solution
                        # to the database. Checking the getAllSolutions function to know what it is considered
                        # to be a solution will raise an error on the evaluation of some programs due to equal
                        # cards.
                        if variable_id in getPredicatesWithAllVariablesBeingInTheSharedSet() |\
                                          getPredicatesWithAllVariablesBeingInTheSharedSetIncludingConstants()|\
                                          getNegatedPredicates():
                            outfile.write('{}data.append_solution_{}({})\n'.format(spaces_level_3,
                                                                                   variable_id.name,
                                                                                   args))
                        
                        # We have to update the database if the identifier pertains to a variable
                        # that is going to be consulted in the database. That means it pertains to
                        # an equation  
                        if variable_id in getAllConsultingPredicates():
                            outfile.write('{}data.insert{}(views.{}, {})\n'.format(spaces_level_3,
                                                                                     pred_length,
                                                                                     view,
                                                                                     args))
                        outfile.write(EMPTY_LINE)
            
                    
            spaces = spaces_level_3
            for equation in equations:
                argument_constants_left_side = [ x for x in equation.leftArguments if x[0].type == 'constant']
                
                if equation.type == 1:
                    # Do we have equal cards? If so we need to be sure they match before process the variable 
                    have_equal_cards = (len(set(equation.leftArguments)) != len(equation.leftArguments))
                    # Check if we have constant arguments (constants propagated trough the datalog source code)
                    if have_equal_cards:
                        temp_dict = defaultdict(list)
                        for rule_pos, (var_name, _) in enumerate(equation.leftArguments, 1):
                            temp_dict[var_name].append(rule_pos)
                            
                        lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                        
                        outfile.write('\n{}if '.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            outfile.write('({})'.format(' == '.join( ['current[{}]'.format(x) for x in l] )))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' and\\\n{}   '.format(spaces))
                    if argument_constants_left_side:
                        if have_equal_cards:
                            outfile.write(' and\\\n{}   '.format(spaces))
                        else:
                            outfile.write('{}if '.format(spaces))
                            
                        for pos, elem in enumerate(argument_constants_left_side):
                            outfile.write('current[{}] == {}'.format(elem[1],
                                                                     str(elem[0].value)))
                            if pos != len(argument_constants_left_side)-1:
                                outfile.write(' and\\\n{}   '.format(spaces))
                            
                    if have_equal_cards or argument_constants_left_side:
                        outfile.write(':\n')
                        spaces += SPACES
                        
                    new_var = 'var = (hypotheses.{}, '.format(equation.rightVariable.id.name)                            
                    for pos, answer in enumerate(equation.rightArguments, 1):
                        # Check if we are dealing with a constant propagated trough the datalog source code.
                        # If we have an integer here it means it is a rewriting constant propagated value
                        # otherwise it is a constant specified on the datalog source code.
                        new_var += compose_expression(answer, None, None)
                            
                        if (pos != len(equation.rightArguments)): new_var += ", "
                        
                    new_var += ')'
                    outfile.write('{}{}'.format(spaces, new_var))
                        
                    common_block(spaces, equation, level,
                                 len(GenerationData.stratums),
                                 idToStratumLevels)
                    
                        
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
                        outfile.write('{}if '.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            outfile.write('({})'.format(' == '.join(['current[{}]'.format(x) for x in l])))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' and\\\n{}   '.format(spaces))
                        if argument_constants_left_side:
                            outfile.write(' and\\\n{}   '.format(spaces))
                                                
                            for pos, elem in enumerate(argument_constants_left_side):
                                outfile.write('current[{}] == {}'.format(elem[1],
                                                                         str(elem[0].value)))
                                if pos != len(argument_constants_left_side)-1:
                                    outfile.write(' and\\\n{}   '.format(spaces))
                                    
                        outfile.write(':\n')
                        spaces += SPACES
                        
                        # Here we have to add the solution to the data structure if the predicate has all variables
                        # the same equal card. We check that if turning the list of leftArguments into a set the
                        # length is 1.
                        if len(set(equation.leftArguments)) == 1:
                            args = ['current[{}]'.format(x) for x in l]
                            outfile.write("{}if not data.contains_solution_{}({}):\n".format(spaces,
                                                                                              equation.leftVariable.id.name,
                                                                                              ", ".join(args)))
                            spaces += SPACES
                            if DEBUG:
                                outfile.write('{}print "\\tAdding solution -> ",\n'.format(spaces))
                                outfile.write('{}print_rewriting_variable(current)\n'.format(spaces))

                            outfile.write("{}data.append_solution_{}({})\n".format(spaces,
                                                                                    equation.leftVariable.id.name,
                                                                                    ", ".join(args)))
                            spaces = spaces[:-len(SPACES)]
                            outfile.write(EMPTY_LINE)
                    
                    elif argument_constants_left_side:
                        outfile.write('{}if '.format(spaces))
                        
                        for pos, elem in enumerate(argument_constants_left_side):
                            outfile.write('current[{}] == {}'.format(elem[1],
                                                                     str(elem[0].value)))
                            if pos != len(argument_constants_left_side)-1:
                                outfile.write(' and\\\n{}   '.format(spaces))
                                
                        outfile.write(':\n')
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
                        outfile.write('{}for t0 in data.get_level0_values():\n'.format(spaces))
                        spaces += SPACES
                        # If the length of the predicate is one we also have to make sure that the value we obtain
                        # is valid as we won't iterate to obtain more values
                        if len(equation.consultingArguments) == 1:
                            outfile.write('{}if (data.contains_solution_{}(t0))'.format(spaces,
                                                                                        equation.consultingPredicate.id.name))
                            outfile.write(':\n')
                    
                    else:
                        # We don't have equal cards in the set of common variables, we just iterate over the set
                        # emitting code appropriately. 
                        if not equal_cards_query_common_vars:
                            args_common = ', '.join(['current[{}]'.format(str(x[1])) for x in equation.commonVariables])
                            #int_length = commonVars_len + len(argument_constants_consulting_values)
                            int_length = commonVars_len + len(argument_constants_consulting_values)
                        # Here we have equal cards in the set of common variables there fore we need to check which is 
                        # the real number of common variables in the query.
                        else:
                            # The number of common variables is just the number of integer values of the consulting values
                            # list
                            number_of_common_vars = sum(1 for x in equation.consultingArguments if isinstance(x, int))
                                                     
                            args_common = ', '.join(['current[{}]'.format(str(x))
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
                            outfile.write('{}for t1 in data.get{}(views.{}, {}):\n'.format(spaces,
                                                                                    int_length + 1,
                                                                                    aliasToViewNames[equation.aliasName],
                                                                                    args_common))
                        else:
                            outfile.write("{}if data.contains_solution_{}({}):\n".format(spaces,
                                                                                         equation.consultingPredicate.id.name,
                                                                                         args_common))
                            spaces += SPACES
    
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
                            outfile.write('{}for t{} in data.get{}(views.{}, {})'.format(spaces,
                                                                                   x,
                                                                                   query_value + 1,
                                                                                   aliasToViewNames[equation.aliasName],
                                                                                   args)) 
                        else:
                            args += ', '.join(['t{}'.format(i) for i in xrange(1, (y-commonVars_len)+1)])
                            outfile.write('{}for t{} in data.get{}(views.{}, {})'.format(spaces,
                                                                                         (y-commonVars_len) + 1,
                                                                                         query_value + 1,
                                                                                         aliasToViewNames[equation.aliasName],
                                                                                         args))

                                          
                        outfile.write(':\n')
                    
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
                        outfile.write('{}if '.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            t = ['t{}'.format(x) for x in l]
                            outfile.write('{}'.format(' == '.join(t)))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' and\\\n{}   '.format(spaces))
                        outfile.write(':\n')
                        spaces += SPACES
                        
                    outfile.write('{}var = (hypotheses.{}'.format(spaces,
                                                                  equation.rightVariable.id.name))
                    
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
                        outfile.write(", {}".format(code))

                    outfile.write(')\n')
                    
                    common_block(spaces, equation, level,
                                 len(GenerationData.stratums),
                                 idToStratumLevels)

                    # Reset the spacing                        
                    outfile.write(EMPTY_LINE)
                    spaces = spaces_level_3
            outfile.write(EMPTY_LINE)

def fillSolverEnd(outfile):
    spaces_level_1 = SPACES
    outputTuples = GenerationData.answersToStore
    
    outfile.write('def solver_end():\n')
    outfile.write('{}global {}\n'.format(spaces_level_1,
                                         ', '.join('fp_{}'.format(ident.name) for ident in outputTuples)))
    for ident in outputTuples:
        outfile.write('{}fp_{}.close()\n'.format(spaces_level_1,
                                                 ident.name))
    outfile.write(EMPTY_LINE)

            
fill_template = {
        'fillAccessViews'   : fillAccessViews,
        'fillHypothesesNames' : fillHypothesesNames,
        'fillSolutions' : fillSolutions,
        'fillInitDataStructure' : fillInitDataStructure,
        'fillCreateNodes': fillCreateNodes,
        'fillInsertNodes': fillInsertNodes,
        'fillGetLevel0Values' : fillGetLevel0Values,
        'fillGetFunctions' : fillGetFunctions,
        'fillContainsFunctions' : fillContainsFunctions,
        'fillAppendFunctions' : fillAppendFunctions,
        'fillPrintRewritingVariable' : fillPrintRewritingVariable,
        'fillPrintAnswer' : fillPrintAnswer,
        'fillStrtatumSolverQueues' : fillStrtatumSolverQueues,
        'fillStratumQueueInitializers' : fillStratumQueueInitializers,
        'fillSolverInit' : fillSolverInit, 
        'fillSolverCompute' : fillSolverCompute,
        'fillSolverEnd' : fillSolverEnd
     }

def fill_file(filename, orig_file, dest_file):
    with open(orig_file, 'r') as infile:
        with open(dest_file, 'w') as outfile:
            # Check if the first line calls fill_Header
            line = infile.readline()
            if line.split()[1] == 'fill_Header':
                header =  '#\n# {}\n'.format(filename)
                header += '# Created by: {}\n'.format('Python Code Generator')
                header += '# Created on: {}\n'.format(datetime.today().date())
                header += '#\n'
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
    path = os.path.normpath(output_directory + '/Solver_Py_code')
    if os.path.exists(path):
        shutil.rmtree(path)
    
    os.makedirs(path)
    
    # Manage the source files
    for source_file in SOURCE_FILES:
        orig_path = os.path.normpath(SOURCE_DIRECTORY + "/" + source_file)
        dest_path = os.path.normpath(path + "/" + source_file)
        fill_file(source_file, orig_path, dest_path)