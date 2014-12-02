'''
Created on Aug 21, 2013

@author: nando
'''

import os
import shutil
import sys

from collections import namedtuple, defaultdict
from itertools import count, chain
from datetime import datetime
from functools import wraps
from Types import Argument

# Settings for the parser
DELIMITER = '%%'
SOURCE_DIRECTORY = "C_Template"
#OUTPUT_DIRECTORY = "./"

INCLUDE_FILES = ['utils.h', 'solver.h', 'data_structure.h', 
                 'data_structure_common.h', 'arena.h','mem.h', 
                 'fact.h', 'parser.h']

SOURCE_FILES = ['makefile', 'main.c', 'parser.c',
                'mem.c', 'data_structure_common.c', 'arena.c',
                'solver.c', 'data_structure.c']

# Global data for the module
GenerationData = None

# Utility functions
def getPredicateLength(predicate):
    for eq in GenerationData.equationsTable:
        if predicate == eq.leftSideName:
            return len(eq.leftSideCons)
        elif predicate == eq.rightSideName:
            return len(eq.rightSideCons)
                   
    return None

def getQueryMinimumLength():
    return min(len(x.leftSideCons) for x in GenerationData.equationsTable if x.type == 2)

def getQueryMaximumLength():
    return max(len(x.leftSideCons) for x in GenerationData.equationsTable if x.type == 2)

# In order to get the minimum node and the maximum node we have to check the right side
# of every rule to store the answers and the left side of the rule of type 2
def getDataStructureNodesMaximumLength():
    return  max(chain([len(x.leftSideCons) for x in GenerationData.equationsTable if x.type == 2],
                      [len(x.rightSideCons) for x in GenerationData.equationsTable]))

# This is a closure to check if we have predicates of type 2, some functions
# like the ones handling the requests to the data structures should not be 
# executed if we don't have predicates of type 2 in the source datalog program.
# Instead of checking that behavior explicitly in the destiny functions 
# this behavior has been extracted as a decorator.
def check_for_predicates_of_type2(view_func):
    def _decorator(request, *args, **kwargs):
        response = None
        # Make sure we don't call the function if we don't have predicates of type 2
        if len([x for x in GenerationData.equationsTable if x.type == 2]):
            response = view_func(request, *args, **kwargs)
        return response
    return wraps(view_func)(_decorator)

# This function checks to see if there are predicates that appearing in some
# rule being all its variables equal cards. 
# The function returns a set of strings, every string represents the name of
# a predicate having all variables as equal cards.
def getPredicatesWithAllVariablesBeingTheSameEqualCard():
    answers = set()
    for rule in GenerationData.equationsTable:
        if (rule.leftSideName not in GenerationData.answersToStore) and\
                len(set(rule.leftSideCons)) == 1 and\
                rule.type == 2:
            answers.add(rule.leftSideName)
    return answers


def getPredicatesWithAllVariablesBeingInTheSharedSet():
    answers = set()
    for rule in GenerationData.equationsTable:
        if (rule.leftSideName not in GenerationData.answersToStore and \
                rule.type == 2 and
                getPredicateLength(rule.consultingPred) == len(rule.common_vars)):
            answers.add(rule.consultingPred)
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
    return solutions

# This function returns a list containing tuples in which the first element
# is a predicate name and the second element is its length.
def getAllPredicatesLengths():
    data = []
    for rule in GenerationData.equationsTable:
        data.append((rule.leftSideName,
                     len(rule.leftSideCons)))
        data.append((rule.rightSideName,
                     len(rule.rightSideCons)))

    # Remove duplicates
    return set(data)

# utils.h
def fillProgramName(outfile):
    outfile.write('#define PROGRAM_NAME "{}"'.format('solver'))
    
def fillHypothesis(outfile):
    hypothesis = set(x.leftSideName for x in GenerationData.equationsTable)
    hypothesis |= set(x.rightSideName for x in GenerationData.equationsTable)
    outfile.write('/* Hipothesys */\n')
    for hypothesis, pos in zip(hypothesis, count()):
        line = '#define {}\t{}\n'.format(hypothesis, str(pos))
        outfile.write(line)
    
def fillAccessViews(outfile):
    sorted_views = GenerationData.viewsData.viewsOrdering
    outfile.write('/* View prefixes */\n')
    for view_name, view_position in sorted_views:
        line = '#define {}\t{}\n'.format(view_name, str(view_position))
        outfile.write(line)
        
# solver.h
def fillRewritingVariable(outfile):
    outfile.write('\tunsigned char PREDICATE;\n\n')
    
    max_length = max(chain((len(x.leftSideCons) for x in GenerationData.equationsTable), 
                           (len(x.rightSideCons) for x in GenerationData.equationsTable)))
    for p in xrange(1, max_length+1):
        outfile.write('\tunsigned int VAR_{};\n'.format(str(p)))
        
# data_structure.h
@check_for_predicates_of_type2
def fillDataStructureQueryHeaderFunctions(outfile):
    min_length = getQueryMinimumLength()
    max_length = getQueryMaximumLength()
    
    for length in xrange(min_length, max_length+1):
        if length == 1:
            ints = ['int' for _ in xrange(length)]
        else:
            ints = ['int' for _ in xrange(length + 1)]

        outfile.write('extern void Ds_insert_{}({});\n'.format(str(length), ', '.join(ints)))
        
    outfile.write('\n')

    ints = ['int', 'int']
    for p in xrange(max_length-1):
        outfile.write('extern intList * Ds_get_intList_{}({});\n'.format(str(p+1), ', '.join(ints)))
        ints.append('int')
        
def fillDataStructureSolutionHeaderFunctions(outfile):
    for solution_predicate in getAllSolutions():
        length = getPredicateLength(solution_predicate)
        ints = ['int' for _ in xrange(length)]
         
        outfile.write('extern int  Ds_contains_solution_{}({});\n'.format(solution_predicate,
                                                                          ', '.join(ints)))
        outfile.write('extern void Ds_append_solution_{}({});\n'.format(solution_predicate,
                                                                        ', '.join(ints)))
    outfile.write('\n')

# solver.c
def fillInputTuplesFiles(outfile):
    extensional = GenerationData.blocksOrder[0]
    outfile.write('static char *tuples_input_files[] = {\n')
    
    for pos, predicate in enumerate(extensional):
        if pos != len(extensional)-1:
            outfile.write('\t"{}.tuples",\n'.format(predicate))
        else:
            outfile.write('\t"{}.tuples"\n'.format(predicate))
    outfile.write('};\n')
    outfile.write('#define INPUT_TUPLES_FILES {}\n'.format(len(extensional)))
    
def fillOutputTuplesFiles(outfile):
    outputTuples = GenerationData.answersToStore
    
    outfile.write('static char *tuples_output_files[] = {\n')
    for pos, predicate in enumerate(outputTuples):
        if pos != len(outputTuples)-1:
            outfile.write('\t"{}.tuples",\n'.format(predicate))
        else:
            outfile.write('\t"{}.tuples"\n'.format(predicate))
    outfile.write('};\n')
    outfile.write('#define OUTPUT_TUPLES_FILES {}\n'.format(len(outputTuples)))
    
    outfile.write('FILE')
    for pos, predicate in enumerate(outputTuples):
        outfile.write(' *fp_{}'.format(predicate))
        if pos != len(outputTuples) - 1:
            outfile.write(',')
    outfile.write(';\n')
    
def fillPrintRewritingVariable(outfile):
    for position, (pred_name, length) in enumerate(getAllPredicatesLengths()):
        if position == 0:
            conditional = 'if'
        else:
            conditional = 'else if'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['b->VAR_' + str(x) for x in xrange(1, length+1)])
        
        outfile.write('\t{} (b->PREDICATE == {})\n'.format(conditional, pred_name))
        outfile.write('\t\tfprintf(file, "X_{}({}).", {});\n'.format(pred_name, formatting, variables))
        
def fillPrintAnswer(outfile):
    for position, (pred_name, length) in enumerate(getAllPredicatesLengths()):
        if position == 0:
            conditional = 'if'
        else:
            conditional = 'else if'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['b->VAR_' + str(x) for x in xrange(1, length+1)])
        
        outfile.write('\t{} (b->PREDICATE == {})\n'.format(conditional, pred_name))
        outfile.write('\t\tfprintf(file, "{}({}).\\n", {});\n'.format(pred_name, formatting, variables))

def fillSolverInit(outfile):
    extensional = GenerationData.blocksOrder[0]
    outputTuples = GenerationData.answersToStore
    
    for pos, predicate in enumerate(extensional):
        length = getPredicateLength(predicate)
        
        outfile.write('\tfp = fopen(tuples_input_files[{}], "r");\n'.format(pos))
        outfile.write('\tif (!fp){\n')
        outfile.write('\t\tfprintf(stderr, "Error: Can\'t open file %s\\n",')
        outfile.write(' tuples_input_files[{}]);\n'.format(pos))
        outfile.write('\t\treturn FALSE;\n')
        outfile.write('\t}\n')
        outfile.write('\twhile (parser_get_fact(fp, NULL, &fact) == 1){\n')
        outfile.write('\t\tVAR.PREDICATE = {};\n'.format(predicate))
        
        for x in xrange(length):
            outfile.write('\t\tVAR.VAR_{} = fact.values[{}];\n'.format(str(x+1), x))

        outfile.write('\n')
        
        formatting = ','.join(['%i' for x in xrange(length)])
        outfile.write('#ifdef NDEBUG\n')
        outfile.write('\t\tfprintf(stderr, "Adding rewriting variable: X_{}'.format(predicate))
        outfile.write('({})\\n",\n'.format(formatting))
        
        for x in xrange(length):
            if x != (length - 1):
                outfile.write('\t\t\t\tVAR.VAR_{},\n'.format(str(x+1)))
            else:
                outfile.write('\t\t\t\tVAR.VAR_{});\n'.format(str(x+1)))
        outfile.write('#endif\n\n')
        
        outfile.write('\t\tSolverQueue_append(&solver, &VAR);\n')
        outfile.write('\t}\n')
        outfile.write('\tfclose(fp);\n\n')
        
    for pos, predicate in enumerate(outputTuples):
        outfile.write('\tfp_{} = fopen(tuples_output_files[{}], "w+");\n'.format(predicate, str(pos)))
    
def fillSolverCompute(outfile):
    def printtemp(tabs, rule):
        # Do we have to store the answer??
        if rule.rightSideName in answersToStore:
            pred = rule.rightSideName

            #if rule.type == 2:
            #    tabs = '\t' * sum(((lambda x: 1 if isinstance(x, str) else 0)(x)\
            #                            for x in rule.consultingValues))
                                
            args = ', '.join('VAR.VAR_{}'.format(x) for 
                            x in xrange(1, len(rule.rightSideCons)+1))
            
            outfile.write('\n{}if (!Ds_contains_solution_{}({}))'.format(tabs,
                                                                         pred,
                                                                         args))
            tabs += '\t'
            outfile.write('{\n')
            outfile.write('#ifdef NDEBUG\n')
            outfile.write('{}fprintf(stderr, "\\tAdding variable -> ");\n'.format(tabs))
            outfile.write('{}print_rewriting_variable(stderr, &VAR);\n'.format(tabs))
            outfile.write('{}fprintf(stderr, "\\n");\n'.format(tabs))
            outfile.write('#endif\n\n')
            
            outfile.write('{}SolverQueue_append(&solver, &VAR);\n'.format(tabs))
            outfile.write('{}Ds_append_solution_{}({});\n'.format(tabs,
                                                                    pred,
                                                                    args))
            tabs = tabs[:-1]
            outfile.write('{}'.format(tabs))
            outfile.write('}\n')
        else:
            outfile.write('{}SolverQueue_append(&solver, &VAR);\n'.format(tabs))
            
    equationsTable = GenerationData.equationsTable
    predsToViewNames = GenerationData.viewsData.predsToViewNames
    viewNamesToCombinations = GenerationData.viewsData.viewNamesToCombinations
    aliasToViewNames = GenerationData.viewsData.aliasToViewNames
    answersToStore = GenerationData.answersToStore
    printVariables = GenerationData.printVariables
    outputTuples = GenerationData.answersToStore
    block1 = GenerationData.blocksOrder[0]
    block2 = GenerationData.blocksOrder[1]
    block3 = GenerationData.blocksOrder[2]
    
    for predicate in chain(block1, block2, block3):
        # Get the rule of the predicate raise an exception if not found
        rules = (x for x in equationsTable
                       if x.leftSideName == predicate)

        outfile.write('\t\tif (current->b.PREDICATE == {})'.format(predicate))
        outfile.write('{\n')
        
        # Do we have to print the variable
        if predicate in printVariables:
            outfile.write("\t\t\tprint_answer(stdout, &current->b);\n")
            
        if predicate in outputTuples:
            outfile.write("\t\t\tprint_answer(fp_{}, &current->b);\n".format(predicate))
        
        # Debug information
        pred_length = getPredicateLength(predicate)
        outfile.write('#ifdef NDEBUG\n')
        formatting = ', '.join(['%i' for _ in xrange(pred_length)])
        args = ',\n\t\t\t\t\t'.join(('current->b.VAR_{}'.format(str(x+1)) for x in xrange(pred_length)))
        output_string = '\t\t\tfprintf(stderr, "Handling rewriting ' +\
                        'variable: X_{}'.format(predicate) +\
                        '({})\\n",\n\t\t\t\t\t{});\n'.format(formatting,
                                                             args)
        outfile.write(output_string)
        #outfile.write('#endif\n')
        
        # Here we emit code to add data to the data structure if we are in a type 2 rule.
        # We emit debugging code via a c macro to check what is going to be added
        # to the data structure. We show the view and the values being added.
        # After we use the appropriate call to add the solution to the data structure
        if predsToViewNames[predicate]:
            # This is the debugging part
            #outfile.write('\n#ifdef NDEBUG\n')
              
            # Debug information: If the predicate has length 1 the it becomes a solution and has to be
            # treated as such. Otherwise we insert a value into the list as normal
            if pred_length == 1:
                outfile.write('\t\t\tfprintf(stderr, "\\tData structure: ')
                outfile.write('Adding solution {}(%i)\\n", current->b.VAR_1);\n'.format(predicate))
            else:
                for view in predsToViewNames[predicate]:
                    args = ', '.join('current->b.VAR_{}'.format(x) for
                                     x in viewNamesToCombinations[view])
                    formatting = ', '.join(('%i' for _ in viewNamesToCombinations[view]))
  
                    outfile.write('\t\t\tfprintf(stderr, "\\tData structure: ')
                    outfile.write('Adding {}({})\\n", {});\n'.format(view,
                                                                    formatting,
                                                                    args))
          
        # This marks the end of the debug information macro this line has to be always emitted as 
        # the portion of the handling the rewriting variable is always emitted and only the
        # adding solution is optional if the predicate is part of a type 2 rule that is there is     
        # a view associated with it
        outfile.write('#endif\n')
        
        # Unfortunately because of the problem of the previous line we have to recheck here if the
        # predicate has a view associated with it
        if predsToViewNames[predicate]:     
            # This is part in which we add the solution to the data structure. If the predicate has length
            # 1 we have to add directly the solution, as by convention there is no level node of length 0
            # and the predicates of length 1 are turned into solutions
            if pred_length == 1:
                outfile.write('\t\t\tDs_append_solution_{}(current->b.VAR_1);\n'.format(predicate))
                outfile.write('\t\t\tDs_insert_1(current->b.VAR_1);\n\n')
            else:
                for view in predsToViewNames[predicate]:
                    args = ', '.join('current->b.VAR_{}'.format(x) for
                                     x in viewNamesToCombinations[view])
                    
                    if predicate in getPredicatesWithAllVariablesBeingInTheSharedSet():
                        outfile.write('\t\t\tDs_append_solution_{}({});\n'.format(predicate,
                                                                                  args))
                    else:
                        outfile.write('\t\t\tDs_insert_{}({}, {});\n'.format(pred_length,
                                                                               view,
                                                                               args))
                    outfile.write('\n')
        
                
        tabs = '\t\t\t'
        for rule in rules:
            argument_constants_left_side = [ x for x in rule.leftSideCons if x[0].type == 'constant']
            
            if rule.type == 1:
                # Do we have equal cards? If so we need to be sure they match before process the variable 
                have_equal_cards = (len(set(rule.leftSideCons)) != len(rule.leftSideCons))
                # Check if we have constant arguments (constants propagated trough the datalog source code
                if have_equal_cards:
                    temp_dict = defaultdict(list)
                    for rule_pos, (var_name, _) in enumerate(rule.leftSideCons, 1):
                        temp_dict[var_name].append(rule_pos)
                        
                    lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                    
                    outfile.write('{}if('.format(tabs))
                    for pos, l in enumerate(lists_of_duplicated_vars):
                        t = ['current->b.VAR_{}'.format(x) for x in l]
                        outfile.write('{}'.format(' == '.join(t)))
                        if pos != len(lists_of_duplicated_vars)-1:
                            outfile.write(' &&\n{}   '.format(tabs))
                if argument_constants_left_side:
                    if have_equal_cards:
                        outfile.write(' &&\n{}   '.format(tabs))
                    else:
                        outfile.write('{}if('.format(tabs))
                        
                    for pos, elem in enumerate(argument_constants_left_side):
                        outfile.write('current->b.VAR_{} == {}'.format(elem[1], 
                                                                       str(elem[0].value)))
                        if pos != len(argument_constants_left_side)-1:
                            outfile.write(' &&\n{}   '.format(tabs))
                        
                if have_equal_cards or argument_constants_left_side:
                    outfile.write('){\n')
                    tabs += '\t'
                        
                outfile.write('{}VAR.PREDICATE = {};\n'.format(tabs, rule.rightSideName))
                for pos, answer_pos in enumerate(rule.rightSideCons, 1):
                    # Check if we are dealing with a constant propagated trough the datalog source code.
                    # If we have an integer here it means it is a rewriting constant propagated value
                    # otherwise it is a constant specified on the datalog source code.
                    if isinstance(answer_pos, int):
                        outfile.write('{}VAR.VAR_{} = current->b.VAR_{};\n'.format(tabs,
                                                                                   str(pos),
                                                                                   str(answer_pos)))
                    else:
                        outfile.write('{}VAR.VAR_{} = {};\n'.format(tabs,
                                                                    str(pos),
                                                                    str(answer_pos.value)))
                    
                printtemp(tabs, rule)
                
                if have_equal_cards or argument_constants_left_side:
                    tabs = tabs[:-1]
                    outfile.write('{}}}\n'.format(tabs, tabs))
                    
            if rule.type == 2:
                #print rule
                commonVars_len = len(rule.common_vars)
                
                argument_constants_consulting_values = [ x for x in rule.consultingValues if
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
                equal_cards_rewriting_variable = (len(set(rule.leftSideCons)) != len(rule.leftSideCons))
                # For the case of the set of common variables is a little bit more complex
                equal_cards_query_common_vars = False
                equal_cards_query_not_common_vars = False
                # We proceed in the same way as before but now we use the consulting Values list
                if (len(set(rule.consultingValues)) != len(rule.consultingValues)):
                    # We start extracting a list with the positions of the variables in the set of 
                    # common variables
                    common_var_positions = set(x[1] for x in rule.common_vars)
                    # Next we obtain how many variables in the consulting values come with the rewriting 
                    # variable that is how many of the we now the position represented as an integer
                    number_of_common_vars = sum(1 for x in rule.consultingValues if isinstance(x, int))
                    # Knowing the number of common variables we can split the list of consulting values
                    # and check for equal values in every part of the list. The first part is used to 
                    # check for if there are equal values in the set of common variables. The last part
                    # of the list is used to check if we have equal cards in the variables we have to 
                    # iterate to obtain new solutions. In this case we also have to check that there are
                    # more than one element otherwise the check for equal values using a set would give
                    # a false positive generating incorrect code
                    for x in rule.consultingValues[:number_of_common_vars]:
                        if x in common_var_positions:
                            equal_cards_query_common_vars = True
                            break
                    if (len(rule.consultingValues[number_of_common_vars:]) > 1) and \
                       (len(rule.consultingValues[number_of_common_vars:]) != \
                            len(set(rule.consultingValues[number_of_common_vars:]))):
                        equal_cards_query_not_common_vars = True

                # If we have equal cards in the rewriting variable we are analyzing to emit code
                # We have to check that the values represented by the equal cards are the same
                if equal_cards_rewriting_variable:
                    # Here we create a dictionary in which every key is a variable name and its
                    # value is its relative position on the list. We have to do it in this way as the
                    # leftSideCons represents a variable with a string and its position in the rule
                    # but if the variable is an equal card the position will be always the same, the 
                    # position of the first occurrence
                    temp_dict = defaultdict(list)
                    for rule_pos, (var_name, _) in enumerate(rule.leftSideCons, 1):
                        temp_dict[var_name].append(rule_pos)
                            
                    # Once we have built the dictionary we create a list of lists removing the lists
                    # of length 1 as the represent the variables that are not equal cards
                    lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                        
                    # Once we have that lists of lists we only have to iterate through to emit the code
                    # Every list will contain the positions that should be equal. We emit an if in which
                    # every line are the positions of the list compared for equality and joined by logical 
                    # ands
                    outfile.write('{}if('.format(tabs))
                    for pos, l in enumerate(lists_of_duplicated_vars):
                        t = ['current->b.VAR_{}'.format(x) for x in l]
                        outfile.write('{}'.format(' == '.join(t)))
                        if pos != len(lists_of_duplicated_vars)-1:
                            outfile.write(' &&\n{}   '.format(tabs))
                    if argument_constants_left_side:
                        outfile.write(' &&\n{}   '.format(tabs))
                                            
                        for pos, elem in enumerate(argument_constants_left_side):
                            outfile.write('current->b.VAR_{} == {}'.format(elem[1], 
                                                                           str(elem[0].value)))
                            if pos != len(argument_constants_left_side)-1:
                                outfile.write(' &&\n{}   '.format(tabs))
                                
                    outfile.write('){\n')
                    tabs += '\t'
                    
                    # Here we have to add the solution to the data structure if the predicate has all variables
                    # the same equal card. We check that if turning the list of leftSideCons into a set the
                    # length is 1.
                    if len(set(rule.leftSideCons)) == 1:
                        args = ['current->b.VAR_{}'.format(x) for x in l]
                        outfile.write("{}if (!Ds_contains_solution_{}({})){{\n".format(tabs,
                                                                                     rule.leftSideName,
                                                                                     ", ".join(args)))
                        tabs += '\t'
                        outfile.write("#ifdef NDEBUG\n")
                        outfile.write("{}fprintf(stderr, \"\\tAdding solution -> \");\n".format(tabs))
                        outfile.write("{}print_rewriting_variable(stderr, &current->b);\n".format(tabs))
                        outfile.write("{}fprintf(stderr, \"\\n\");\n".format(tabs))
                        outfile.write("#endif\n")
                        outfile.write("{}Ds_append_solution_{}({});\n".format(tabs,
                                                                             rule.leftSideName,
                                                                             ", ".join(args)))
                        tabs = tabs[:-1]
                        outfile.write("{}}}\n".format(tabs))
                
                # NO ESTOY MUY SEGURO DE QUE ESTO VAYA AQUI DE MOMENTO EN LOS TESTS FUNCIONA PERO HAY QUE HACER MAS PRUEBAS.
                elif argument_constants_left_side:
                    outfile.write('{}if('.format(tabs))
                    
                    for pos, elem in enumerate(argument_constants_left_side):
                        outfile.write('current->b.VAR_{} == {}'.format(elem[1],
                                                                       str(elem[0].value)))
                        if pos != len(argument_constants_left_side)-1:
                            outfile.write(' &&\n{}   '.format(tabs))
                            
                    outfile.write('){\n')
                    tabs += '\t'
                    
                
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
                    outfile.write('{}Ds_get_intValues_Level0_init();\n'.format(tabs))
                    outfile.write('{}while(Ds_get_intValues_Level0(&t0)'.format(tabs))
                    # If the length of the predicate is one we also have to make sure that the value we obtain
                    # is valid as we won't iterate to obtain more values
                    if len(rule.consultingValues) == 1:
                        outfile.write(' && (Ds_contains_solution_{}(t0))'.format(rule.consultingPred))
                    outfile.write('){\n')

                else:
                    # We don't have equal cards in the set of common variables, we just iterate over the set
                    # emitting code appropriately. 
                    if not equal_cards_query_common_vars:
                        args_common = ', '.join(['current->b.VAR_{}'.format(str(x[1])) for x in rule.common_vars])
                        #int_length = commonVars_len + len(argument_constants_consulting_values)
                        int_length = commonVars_len + len(argument_constants_consulting_values)
                    # Here we have equal cards in the set of common variables there fore we need to check which is 
                    # the real number of common variables in the query.
                    else:
                        # The number of common variables is just the number of integer values of the consulting values
                        # list
                        number_of_common_vars = sum(1 for x in rule.consultingValues if isinstance(x, int))
                                                 
                        args_common = ', '.join(['current->b.VAR_{}'.format(str(x))
                                                 for x in rule.consultingValues[:number_of_common_vars]])
                            
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
                    #if (len(set(rule.consultingValues)) != 1 and\
                    #    getPredicateLength(rule.consultingPred) != len(rule.common_vars)):
                    if (len(set([x for x in rule.consultingValues if not (isinstance(x, Argument) and x.type=='constant')])) != 1 and\
                        getPredicateLength(rule.consultingPred) != len(rule.common_vars)):
                        # Here we just emit code for t1 using the computed values
                        outfile.write('{}t1 = Ds_get_intList_{}({}, {});\n'
                                      .format(tabs,
                                              int_length,
                                              aliasToViewNames[rule.aliasName],
                                              args_common))
                        
                        outfile.write('{}for (; t1; t1 = t1->next){{\n'.format(tabs))
                    else:
                        outfile.write("{}if (Ds_contains_solution_{}({})){{\n".format(tabs,
                                                                                     rule.consultingPred,
                                                                                     args_common))

                # Here we emit code for the rest of the required t levels that value is the number
                # of consulting values minus the number of common variables which has already been
                # used in the t1 level
                start = 2
                if commonVars_len == 0:
                    start = 1
                for (x, y) in enumerate(xrange(commonVars_len + 1, 
                                               len(rule.consultingValues) - len(argument_constants_consulting_values)),
                                        start=start):
                    query_value = y + len(argument_constants_consulting_values)
                    if commonVars_len == 0:
                        args = 't0'
                        if x > 1: args += ', '
                        tabs = tabs + '\t' * x
                    else:
                        args = args_common + ', '
                        tabs = tabs + '\t' * (x - 1)
                       
                    if not equal_cards_query_common_vars:
                        args += ', '.join(['t{}->value'.format(str(i))
                                           for i in xrange(1, x)])
                        
                        outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                                      .format(tabs, x, query_value,
                                              aliasToViewNames[rule.aliasName],
                                              args))
                        #number_of_args = y + len(argument_constants_consulting_values)
                        #outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                        #              .format(tabs, x, number_of_args,
                        #                      aliasToViewNames[rule.aliasName],
                        #                      args))
                        outfile.write('{0}for (; t{1}; t{1} = t{1}->next)'.format(tabs,
                                                                                  str(x)))
                    else:
                        #outfile.write("X: {}\t\tARGS:{}\t\tNUMBER_OF_ARGS: {}\t\tY: {}\t\tCOMMON_VARS: {}\n".format(x, args, number_of_args, y, commonVars_len))
                        args += ', '.join(['t{}->value'.format(str(i))
                                           for i in xrange(1, (y-commonVars_len)+1)])

                        outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                                      .format(tabs, (y-commonVars_len)+1, query_value,
                                              aliasToViewNames[rule.aliasName],
                                              args))
                        #number_of_args = y + len(argument_constants_consulting_values)
                        #outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                        #              .format(tabs, (y-commonVars_len)+1, number_of_args,
                        #                      aliasToViewNames[rule.aliasName],
                        #                      args))
                        outfile.write('{0}for (; t{1}; t{1} = t{1}->next)'.format(tabs,
                                                                                  str((y-commonVars_len) + 1)))
                                      
                    outfile.write('{\n')
                
                # ANADIDO or argument_constants_left_side PARA EQUILIBRAR EL NUMERO DE TABS
                if equal_cards_rewriting_variable or argument_constants_left_side\
                 or argument_constants_consulting_values:
                    tabs = '\t\t\t\t'
                else:
                    tabs = '\t\t\t'
                tabs += '\t' * sum(((lambda x: 1 if isinstance(x, Argument) and x.type == 'variable' else 0)(x) 
                                        for x in rule.consultingValues))
                
                outfile.write('{}VAR.PREDICATE = {};\n'.format(tabs,
                                                               rule.rightSideName))
                # Here we handle if we have equal cards in the query variables that are
                # not in the set of common variables. As we retrieve them from the iterating
                # lists we have to check that are equal otherwise we would count
                # invalid answers not honoring the equal cards. To do so we have to check
                # which of the variables not in the set of the common variables are repeated
                if equal_cards_query_not_common_vars:
                    if len(set(rule.consultingValues)) != 1:
                        # The key of the dict will be the name of the variable.
                        # The value of the dict will be a list containing the positions in which
                        # the variable appears repeated
                        temp_dict = defaultdict(list)
                        # Here we compute the first occurrence of the variables.
                        # We compute where the first string appears in the list.
                        number_of_common_vars = sum(1 for x in rule.consultingValues if isinstance(x, int))
                        # Here we iterate over the list of variables that are not in the set of common variables. The
                        # variables start after the variables that belong to the set of common variables and are represented 
                        # by its string name. We have to subtract the number of common variables as the first iterating variable
                        # is always t1 and not t? being ? the position its the list of consultingValues
                        for rule_pos, var_name in enumerate(rule.consultingValues[number_of_common_vars:], number_of_common_vars+1):
                            temp_dict[var_name].append(rule_pos - number_of_common_vars - len(argument_constants_consulting_values))
                              
                        # Here we create a lists of lists removing the lists of only one member as that implies 
                        # that is not a duplicated variable. Every list will contain the position of the duplicated 
                        # variables
                        lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                    else:
                        lists_of_duplicated_vars = [list(xrange(len(rule.consultingValues)))]
                        
                    # We only have to iterate over each list emitting code appropriately 
                    outfile.write('{}if('.format(tabs))
                    for pos, l in enumerate(lists_of_duplicated_vars):
                        t = ['t{}'.format(x) for x in l]
                        t = map(lambda x: x if (x == "t0") else x + "->value", t)
                        outfile.write('{}'.format(' == '.join(t)))
                        if pos != len(lists_of_duplicated_vars)-1:
                            outfile.write(' &&\n{}   '.format(tabs))
                    outfile.write('){\n')
                    tabs += '\t'
                
                # Here we emit code to create the new variable. We start iterating
                # from the rightSideCons and check for every variable position of the
                # answer which other variable goes if it is a variable name we check
                # which of the "t" values is required. The "t" values are used to 
                # iterate over the set of common vars. If is just a number it means
                # it comes from the variable so we just to use that value. We also have
                # to handle the case in which there are no common variables for that case
                # we start at t0 as we have to iterate over all the variables of the other
                # predicate.
                for pos, var in enumerate(rule.rightSideCons, start=1):
                    outfile.write('{}VAR.VAR_{} = '.format(tabs, pos))
                    if isinstance(var, Argument) and var.type == 'variable':
                        t_index = rule.consultingValues.index(var) + 1\
                                   - commonVars_len - len(argument_constants_consulting_values)
                        if commonVars_len == 0:
                            if t_index == 1:
                                outfile.write('t0;\n')
                            else:
                                outfile.write('t{}->value;\n'.format(str(t_index-1)))
                        else:
                            outfile.write('t{}->value;\n'.format(str(t_index)))
                    elif isinstance(var, Argument) and var.type == 'constant':
                        outfile.write('{};\n'.format(str(var.value)))
                    else:
                        outfile.write('current->b.VAR_{};\n'.format(str(var)))
                
                # Here we just emit source code to handle the indentation and the closing }
                # TODO: The indentation is a little bit broken right now and should be checked
                #       but is not mandatory for the well functioning of the compiler
                if equal_cards_query_not_common_vars:
                    printtemp(tabs[:-1], rule)
                else:
                    printtemp(tabs, rule)

                if equal_cards_rewriting_variable or argument_constants_left_side:
                    tabs = tabs[:-1]
                    outfile.write('{}}}\n'.format(tabs))
                    
                if equal_cards_query_not_common_vars:
                    tabs = tabs[:-1]
                    outfile.write('{}}}\n'.format(tabs))
                
                for x in xrange(commonVars_len+1, len(rule.consultingValues) - len(argument_constants_consulting_values)):
                    tabs = tabs[:-1]
                    outfile.write('{}'.format(tabs))
                    outfile.write('}\n')
                    
                outfile.write('\t\t\t}\n')
        outfile.write('\t\t}\n\n')
        
# In this function we emit code to close the file descriptors opened before
# to store the answers in files. The file descriptor is called fp_{} plus the
# name of the predicate.
def fillSolverFree(outfile):
    outputTuples = GenerationData.answersToStore
    
    for predicate in outputTuples:
        outfile.write('\tfclose(fp_{});\n'.format(predicate))

@check_for_predicates_of_type2
def fillIntList(outfile):
    equationsTable = GenerationData.equationsTable
    
    # Check if there is a rule without common variables if that is the case we
    # need to iterate over the first level of the data structure at some point
    # and we need an extra variable to deal with it as we don't store list
    # of integers for the first level.
    requires_t0 = any(len(x.common_vars) == 0 for x in equationsTable if x.type == 2)
    # Obtain the number of variables we have to iterate over to generate new 
    # answers. That value is the number of variables in the consulting values list
    length = max(len(filter(lambda y: isinstance(y, Argument) and y.type == 'variable', x.consultingValues)) 
                    for x in equationsTable if x.type == 2)
    
    # In case there is a rule with no common variables
    if requires_t0:
        outfile.write('\tunsigned int t0;\n')
        
        # Check if the longest length comes from a rule with no common variables
        # if that is the case then we have to subtract 1 to the value as we are already 
        # using t0. 
        no_cvars_max_length = max(len(filter(lambda y: isinstance(y, Argument) and y.type == 'variable', x.consultingValues)) 
                                  for x in equationsTable if x.type == 2 and len(x.common_vars) == 0)
        
        if no_cvars_max_length == length:
            length -= 1
            
    args = ', '.join(['*t{}'.format(str(x+1)) for x in xrange(length)])

    # If in the end the length is 0 that means that the intList will be empty. In that
    # case doesn't make too much sense to emit code for it as it would only trigger a
    # warning from the c compiler
    if length > 0:
        outfile.write('\tintList {};\n'.format(args))

def fillDataStructureLevelNodes(outfile):
    equationsTable = GenerationData.equationsTable
    answersToStore = GenerationData.answersToStore
    viewNamesToCombinations = GenerationData.viewsData.viewNamesToCombinations
    
    # Store the answers by length. This will be used to know in which level node store the
    # answers
    lengthToPreds = defaultdict(set)
    for rule in equationsTable:
        if len(rule.rightSideCons) > 1:
            lengthToPreds[len(rule.rightSideCons)].add(rule.rightSideName)
            
    
    viewsData = []        
    viewLengths = list((len(x) for x in viewNamesToCombinations.itervalues()))
    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    
    lengths = list(xrange(2, number_of_data_structure_nodes+1))
    for length in lengths:
        viewsData.append((length, viewLengths.count(length)))

    for pos, length in enumerate(lengths):
        number_of_views_for_this_level = sum((x[1]) for x in viewsData 
                                             if x[0] >= length)

        outfile.write('struct DsData_Level_{}'.format(length))
        outfile.write('{\n')
        tabs = '\t'
        # If the number of views for this level is 0 we don't have to emit code
        # to store the intList for the current level, also it would output m[0]
        # forbidden by ISO C and with no sense.
        if number_of_views_for_this_level:
            outfile.write('{}intList *m[{}];\n'.format(tabs,
                                                       number_of_views_for_this_level))
        
        # Emit code to store the answers required by the level node
        for pred in lengthToPreds[length]:
            if pred in answersToStore:
                outfile.write('{}Pvoid_t R{};\n'.format(tabs, pred))
                
        # Check if we have to add a new solution because there is a predicate having
        # all the variables the same Equal card or there is a predicate having all
        # its variables part of the set of common variables  
        for pred in chain(getPredicatesWithAllVariablesBeingTheSameEqualCard(),
                          getPredicatesWithAllVariablesBeingInTheSharedSet()):
            if pred not in answersToStore and getPredicateLength(pred) == length:
                outfile.write('{}Pvoid_t R{};\n'.format(tabs, pred))
               
        if pos != len(lengths) - 1:
            # This is purely esthetic if we have some views in the level we 
            # print a blank line to split the intList declaration from the
            # level declaration clearly
            if number_of_views_for_this_level:
                outfile.write('\n')
            outfile.write('{}Pvoid_t level{};\n'.format(tabs, length+1))
            
        outfile.write('};\n')
        outfile.write('typedef struct DsData_Level_{0} DsData_{0};\n\n'.format(length))
        
        outfile.write('DsData_{0} * DsData_Level_{0}_new_node();\n'.format(length))
        outfile.write('void DsData_Level_{0}_init(DsData_{0} *);\n'.format(length))
        outfile.write('void DsData_Level_{0}_free(DsData_{0} *);\n'.format(length))
        outfile.write('\n\n')
        
    outfile.write('\n')

@check_for_predicates_of_type2    
def fillDataStructureInsertFunctions(outfile):
    def print_code_for_Ds_insert_1():
        tabs = '\t'
        outfile.write('void Ds_insert_1(int x_1){\n')
        outfile.write('{}Word_t * PValue1;\n\n'.format(tabs))
        outfile.write('{}if (!(JLG(PValue1, root, x_1))){{\n'.format(tabs))
        tabs += '\t'
        outfile.write('{}JLI(PValue1, root, x_1);\n'.format(tabs))
        outfile.write('{}if (PValue1 == PJERR){{\n'.format(tabs))
        tabs += '\t'
        outfile.write('{}fprintf(stderr, "Solver: Error allocating '.format(tabs))
        outfile.write('memory %s:%i\\n", __FILE__, __LINE__);\n')
        outfile.write('{}abort();\n'.format(tabs))
        tabs = tabs[:-1]
        outfile.write('{}}}\n'.format(tabs))
        if getDataStructureNodesMaximumLength() > 1:
            outfile.write('{}(*PValue1) = ((Word_t) DsData_Level_2_new_node());\n'.format(tabs))
        tabs = tabs[:-1]
        outfile.write('{}}}\n'.format(tabs))
        outfile.write('}\n')

    # Here we emit code to deal with the views. The length of the views is the same of the
    # length of the predicate it represents. Views can only exist for predicates on the 
    # right side of the rules so we take the minimum and maximum lengths of the predicates
    # of right side of the rules and emit functions for those values and the values in between
    # As we don't store a level 1 node if the minimum length we have is 1, we need to
    # emit slightly different code that is why the auxiliary function print_code_for_Ds_insert_1()
    # is created and called if we detect a minimum length of 1
    lengths = xrange(getQueryMinimumLength(), getQueryMaximumLength()+1)
    
    for length in lengths:
        # We have to handle length 1 differently. If we detect that the current length is 1 as we don't
        # have a level 1 node for the data structure we have to emit code differently that is why the
        # auxiliary function code_for_Ds_insert_1 is invoked and then we continue the to the next length.
        # We do it in this way as is easier to create an auxiliary function for this case that to add
        # checks for the control flow to detect if we are in the length 1 case every time we emit code.
        if length == 1:
            print_code_for_Ds_insert_1()
            continue

        args_to_function = ('int x_{}'.format(str(v+1)) for v in xrange(length))
        outfile.write('void Ds_insert_{}(int pos, {})'.format(length,
                                                              ", ".join(args_to_function)))
        outfile.write('{\n')
        tabs = '\t'
        values = ('* PValue{}'.format(str(v+1)) for v in xrange(length-1))
        outfile.write('{}Word_t {};\n\n'.format(tabs,
                                              ', '.join(values)))
        
        for x in xrange(1, length):
            if x == 1:
                node = 'root'
            else:
                node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)
            
            outfile.write('{0}if (!(JLG(PValue{1}, {2}, x_{1})))'.format(tabs, x, 
                                                                         node))
            outfile.write('{\n')
            tabs += '\t'
            outfile.write('{0}JLI(PValue{1}, {2}, x_{1});\n'.format(tabs, x, 
                                                                    node))
            outfile.write('{0}if (PValue{1} == PJERR)'.format(tabs, x))
            outfile.write('{\n')
            tabs += '\t'
            outfile.write('{}fprintf(stderr, "Solver: Error '.format(tabs))
            outfile.write('allocating memory %s:%i\\n", __FILE__, __LINE__);\n')
            
            outfile.write('{}abort();\n'.format(tabs))
            tabs = tabs[:-1]
            outfile.write('{}'.format(tabs))
            outfile.write('}\n')
            outfile.write('{}(*PValue{}) = ((Word_t) DsData_Level_{}_new_node());\n'.format(tabs, 
                                                                                             x, x+1))
            tabs = tabs[:-1]
            outfile.write('{}'.format(tabs))
            outfile.write('}\n\n')
            
        for x in xrange(2, length+1):
            outfile.write('{}intList_append(&((DsData_{} *)'.format(tabs, x))
            outfile.write(' *PValue{})->m[pos], x_{});\n'.format(x-1, x))
            
        outfile.write('}\n\n')

@check_for_predicates_of_type2        
def fillDataStructureGetIntListFunctions(outfile):
    equationsTable = GenerationData.equationsTable
    
    # Here we emit source code for the functions to retrieve the lists we need
    # to iterate to obtain new solutions basically we have to add a new 
    # function for every variable previously emitted in the fillIntList 
    # function in this module. As we have to emit code for those variables the
    # way in which the value is computed is the same. May be this functionality
    # could be refactored into a new function. For more detailed explanation on
    # how to compute those values please check the fillIntList function
    
    requires_t0 = any(len(x.common_vars) == 0 for x in equationsTable if x.type == 2)
    length = getQueryMaximumLength() - 1
    
    if requires_t0:
        no_cvars_max_length = max(len(x.consultingValues) for x in equationsTable
                                  if x.type == 2 and len(x.common_vars) == 0)
        if no_cvars_max_length == length:
            length -= 1
            
    # This loop is in charge to emit the source code of the different functions 
    # required to retrieve the different lists. We add one to the length as the
    # xrange functions goes to length - 1. We start in 1 as the 0 value is
    # reserved in the template to retrieve the values of the root.
    for length in xrange(1, length+1):
        args_to_function = ('int x_{}'.format(str(v+1)) for v in xrange(length))
        outfile.write('intList * Ds_get_intList_{}(int pos, {})'.format(length,
                                                              ", ".join(args_to_function)))
        outfile.write('{\n')
        tabs = '\t'
        values = ('* PValue{}'.format(str(v+1)) for v in xrange(length))
        outfile.write('{}Word_t {};\n\n'.format(tabs,
                                              ', '.join(values)))
        
        for x in xrange(1, length+1):
            if x == 1:
                node = 'root'
            else:
                node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)

            outfile.write('{}if ((JLG(PValue{}, {}, x_{})))'.format(tabs, str(x),
                                                                    node, str(x)))
            outfile.write('{\n')
            tabs += '\t'
            
        outfile.write('{}return ((DsData_{} *) '.format(tabs,
                                                        str(length+1)))
        
        outfile.write('*PValue{})->m[pos];\n'.format(str(length)))
        
        for x in xrange(1, length+1):
            tabs = tabs[:-1]
            outfile.write('{}'.format(tabs))
            outfile.write('}\n')
        
        outfile.write('\n{}return NULL;\n'.format(tabs))
        
        outfile.write('}\n\n')
        
def fillDataStructureContainSolutionFunctions(outfile):
    for solution_predicate in getAllSolutions():
        # Get the length of the predicate
        length = getPredicateLength(solution_predicate)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('int Ds_contains_solution_{}({})'.format(solution_predicate,
                                                               ', '.join(args)))
        outfile.write('{\n')
        tabs = '\t'
        if length > 1:
            values = ('* PValue{}'.format(str(v+1)) for v in xrange(length-1))
            outfile.write('{}Word_t {};\n\n'.format(tabs,
                                                    ', '.join(values)))
        
        for x in xrange(1, length):
            if x == 1:
                node = 'root'
            else:
                node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)
                
            outfile.write('{0}if (!(JLG(PValue{1}, {2}, x_{1})))\n'.format(tabs, x,
                                                                           node))
            tabs += '\t'
            outfile.write('{}return FALSE;\n'.format(tabs))
            tabs = tabs[:-1]
            
        if length > 1:
            outfile.write('\n')
            node = '((DsData_{} *) *PValue{})->R{}'.format(str(length),
                                                           str(length-1),
                                                           solution_predicate)
        else:
            node = 'R{}'.format(solution_predicate)
        outfile.write('{}return Judy1Test({}, x_{}, PJE0);\n'.format(tabs, node,
                                                                   length))
        
        outfile.write('}\n\n')
        
def fillDataStructureAppendSolutionFunctions(outfile):
    for solution_predicate in getAllSolutions():
        # Get the length of the predicate
        length = getPredicateLength(solution_predicate)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('void Ds_append_solution_{}({})'.format(solution_predicate,
                                                               ', '.join(args)))
        outfile.write('{\n')
        tabs = '\t'
        if length > 1:
            values = ('* PValue{}'.format(str(v+1)) for v in xrange(length-1))
            outfile.write('{}Word_t {};\n\n'.format(tabs,
                                                    ', '.join(values)))
        for x in xrange(1, length):
            if x == 1:
                node = 'root'
            else:
                node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)
            
            outfile.write('{0}if (!(JLG(PValue{1}, {2}, x_{1})))'.format(tabs, x, 
                                                                         node))
            outfile.write('{\n')
            tabs += '\t'
            outfile.write('{0}JLI(PValue{1}, {2}, x_{1});\n'.format(tabs, x, 
                                                                    node))
            outfile.write('{0}if (PValue{1} == PJERR)'.format(tabs, x))
            outfile.write('{\n')
            tabs += '\t'
            outfile.write('{}fprintf(stderr, "Solver: Error '.format(tabs))
            outfile.write('allocating memory %s:%i\\n", __FILE__, __LINE__);\n')
            
            outfile.write('{}abort();\n'.format(tabs))
            tabs = tabs[:-1]
            outfile.write('{}'.format(tabs))
            outfile.write('}\n')
            outfile.write('{}(*PValue{}) = ((Word_t) DsData_Level_{}_new_node());\n'.format(tabs, 
                                                                                             x, x+1))
            tabs = tabs[:-1]
            outfile.write('{}'.format(tabs))
            outfile.write('}\n\n')
        
        if length > 1:
            node = '((DsData_{} *) *PValue{})->R{}'.format(str(length),
                                                           str(length-1),
                                                           solution_predicate)
        else:
            node = 'R{}'.format(solution_predicate)
        
        outfile.write('{}if (Judy1Set(&{}, x_{}, PJE0) == JERR)'.format(tabs,
                                                                        node,
                                                                        str(length)))
        outfile.write('{\n')
        tabs += '\t'
        outfile.write('{}fprintf(stderr, "Solver: Error '.format(tabs))
        outfile.write('allocating memory %s:%i\\n", __FILE__, __LINE__);\n')
        outfile.write('{}abort();\n'.format(tabs))
        tabs = tabs[:-1]
        outfile.write('{}'.format(tabs))
        outfile.write('}\n')
        
        outfile.write('}\n\n')

@check_for_predicates_of_type2  
def fillDataStructureInitLevelFunctions(outfile):
    equationsTable = GenerationData.equationsTable
    answersToStore = GenerationData.answersToStore
    viewNamesToCombinations = GenerationData.viewsData.viewNamesToCombinations

    lengthToPreds = defaultdict(set)
    for rule in equationsTable:
        if len(rule.rightSideCons) > 1:
            lengthToPreds[len(rule.rightSideCons)].add(rule.rightSideName)
        
    viewLengths = list((len(x) for x in viewNamesToCombinations.itervalues()))
    viewsData = []
    
    # As we don't store a level0 type of node the minimum length we can have here is 2, that 
    # is the reason why the max value between the minimum query value and 2 is used.
    lengths = xrange(max(getQueryMinimumLength(), 2), getQueryMaximumLength()+1)
    for length in lengths:
        viewsData.append((length, viewLengths.count(length)))

    for pos, length in enumerate(lengths):
        number_of_views_for_this_level = sum((x[1]) for x in viewsData 
                                             if x[0] >= length)
        
        outfile.write('void DsData_Level_{0}_init(DsData_{0} *d)'.format(length))
        outfile.write('{\n')
        tabs = '\t'
        
        outfile.write('{}'.format(tabs))
        for i in xrange(number_of_views_for_this_level):
            outfile.write('d->m[{}] = '.format(i))
                
            if ((i%4) == 0 and i > 0):
                outfile.write('NULL;\n');
                if i != (number_of_views_for_this_level-1):
                    outfile.write('{}'.format(tabs));
                
        if (((number_of_views_for_this_level-1) % 4) != 0 or
            (number_of_views_for_this_level == 1)):
                outfile.write('NULL;\n');
            
        outfile.write('\n')
        if pos != len(lengths)-1:
            outfile.write('{}d->level{} = (Pvoid_t) NULL;\n'.format(tabs, length + 1))
            
        for pred in lengthToPreds[length]:
            if pred in answersToStore:
                outfile.write('{}d->R{} = (Pvoid_t) NULL;\n'.format(tabs, pred))
            
        outfile.write('}\n')
   
def fillDataStructureLevelNewNodeFunctions(outfile):
    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    # This checks that we don't handle level 1 nodes as for the current generation model doesn't 
    # contemplate the possibility of having a level 1 node. 
    #if min_value == 1: min_value += 1
    #lengths = xrange(min_value, number_of_data_structure_nodes + 1)
    lengths = xrange(2, number_of_data_structure_nodes + 1)
    
    for length in lengths:
        node = 'DsData_{}'.format(length)
        outfile.write('{} * DsData_Level_{}_new_node()'.format(node,
                                                               length))
        tabs = '\t'
        outfile.write('{\n')
        outfile.write('{}{} * temp;\n\n'.format(tabs, node))
        outfile.write('{}ARENA_ALLOC(temp);\n'.format(tabs))
        outfile.write('{}memset(temp, 0, sizeof({}));\n\n'.format(tabs, node))
        outfile.write('{}return temp;\n'.format(tabs))
        outfile.write('}\n\n')

def fillDataStructureLevelFreeFunctions(outfile):
    equationsTable = GenerationData.equationsTable
    answersToStore = GenerationData.answersToStore

    # This checks that we don't handle level 1 nodes as for the current generation model doesn't 
    # contemplate the possibility of having a level 1 node.
    #if min_value == 1: min_value += 1
    #lengths = xrange(min_value, max_value + 1)
    lengths = xrange(2, getDataStructureNodesMaximumLength() + 1)
    
    lengthToPreds = defaultdict(set)
    for rule in equationsTable:
        lengthToPreds[len(rule.rightSideCons)].add(rule.rightSideName)
        
    for pos, length in enumerate(lengths):
        outfile.write('void DsData_Level_{0}_free(DsData_{0} *d)'.format(length))
        tabs = '\t'
        outfile.write('{\n')
        if pos != len(lengths) - 1:
            outfile.write('{}Word_t * PValue, index = 0;\n\n'.format(tabs))
            outfile.write('{}JLF(PValue, d->level{}, index);\n'.format(tabs,
                                                                       length+1))
            outfile.write('{}while (PValue != NULL)'.format(tabs))
            outfile.write('{\n')
            tabs += '\t'
            outfile.write('{0}DsData_Level_{1}_free((DsData_{1} *) *PValue);\n'.format(tabs,
                                                                                       length+1))
            outfile.write('{}JudyLDel(&d->level{}, index, PJE0);\n'.format(tabs,
                                                                         length+1))
            outfile.write('{}JLN(PValue, d->level{}, index);\n'.format(tabs,
                                                                     length+1))
            tabs = tabs[:-1]
            outfile.write('{}'.format(tabs))
            outfile.write('}\n')
        
        for pred in lengthToPreds[length]:
            if pred in answersToStore:
                outfile.write('{}Judy1FreeArray(&d->R{}, PJE0);\n'.format(tabs,
                                                                          pred))
                
        outfile.write('{}*&d = NULL;\n'.format(tabs))        
        outfile.write('}\n\n')

# As the level 1 node is currently treated diferently from the other type of nodes  
# levels is necessary to store the solutions formed by heads of length 1, also if we 
# have body predicates of length 1 in the rules they became solutions.
def fillDataStructureRootSolutions(outfile):
    answers_of_length_1 = set()
    predicates_in_rules_of_length_1 = set()
    for rule in GenerationData.equationsTable:
        if len(rule.rightSideCons) == 1:
            answers_of_length_1.add(rule.rightSideName)
        if len(rule.leftSideCons) == 1:
            predicates_in_rules_of_length_1.add(rule.leftSideName)
            
    if answers_of_length_1:
        outfile.write("/* Solution of length 1 */\n")
        line = ', '.join(['R{}'.format(answer) for answer in answers_of_length_1])
        outfile.write('static Pvoid_t {};\n'.format(line))
        
    if predicates_in_rules_of_length_1:
        outfile.write("/* Predicates of length 1*/\n")
        line = ', '.join(['R{}'.format(answer) for answer in predicates_in_rules_of_length_1])
        outfile.write('static Pvoid_t {};\n'.format(line))

# This function only should be executed if there are predicates of length 2
# If we only have type 1 rules we don't have level 2 nodes (as there is no database) 
# so this will cause an error. Another case we have to handle is that if even having
# rules of type 2 the maximum length is 1. 
@check_for_predicates_of_type2
def fillDataStructureLevel2Line(outfile):
    if getDataStructureNodesMaximumLength() > 1:
        outfile.write('\t\tDsData_Level_2_free((DsData_2 *) *PValue);\n')

# Function mapping for directives
fill_template = {
     'fill_ProgramName'  : fillProgramName,
     'fill_Hypothesis'   : fillHypothesis,
     'fill_AccessViews'  : fillAccessViews,
     'fill_RewritingVariable'   : fillRewritingVariable,
     'fill_InputTuplesFiles'       : fillInputTuplesFiles,
     'fill_OutputTuplesFiles'      : fillOutputTuplesFiles,
     'fill_PrintRewritingVariable' : fillPrintRewritingVariable,
     'fill_PrintAnswer'         : fillPrintAnswer,
     'fill_SolverInit'          : fillSolverInit,
     'fill_SolverCompute'       : fillSolverCompute,
     'fill_SolverFree'          : fillSolverFree,
     'fill_IntList'             : fillIntList,
     'fill_DsQueryHeaderFunctions' : fillDataStructureQueryHeaderFunctions,
     'fill_DsSolutionHeaderFunctions' : fillDataStructureSolutionHeaderFunctions,
     'fill_DsLevelNodes'  : fillDataStructureLevelNodes,
     'fill_DsInsertFunctions' : fillDataStructureInsertFunctions,
     'fill_DsGetIntListFunctions': fillDataStructureGetIntListFunctions,
     'fill_DsContainSolutionFunctions' : fillDataStructureContainSolutionFunctions,
     'fill_DsAppendSolutionFunctions'  : fillDataStructureAppendSolutionFunctions,
     'fill_DsLevelInitLevelFunctions' : fillDataStructureInitLevelFunctions,
     'fill_DsLevelNewNodeFunctions' : fillDataStructureLevelNewNodeFunctions,
     'fill_DsLevelFreeFunctions' : fillDataStructureLevelFreeFunctions,
     'fill_DsRootAnswers'        : fillDataStructureRootSolutions,
     'fill_DsFreeLevel2Line'     : fillDataStructureLevel2Line
     }

 
def fill_file(filename, orig_file, dest_file):
    with open(orig_file, 'r') as infile:
        with open(dest_file, 'w') as outfile:
            # Check if the first line calls fill_Header
            line = infile.readline()
            if line.split()[1] == 'fill_Header':
                header = '/*\n * {}\n *\n'.format(filename)
                header += ' * Created by: {}\n'.format('C Code Generator')
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
                    except KeyError:
                        print "Error: {}: {}: Unknown directive: {}".format(filename, 
                                                                   line_number,
                                                                   function)
                        sys.exit(-1)
                else:
                    outfile.write(line)
                    
    return True
              
def generate_code_from_template(output_directory, equationsTable, viewsData,
                                blocksOrder, predicateTypes, 
                                answersToStore, printVariables):
    # Make the necessary data to generate the source code available to the rest of the functions
    GD = namedtuple('GD', ['equationsTable', 'viewsData', 
                           'predicateTypes', 'blocksOrder',
                           'answersToStore', 'printVariables'])
    
    globals()['GenerationData'] = GD(equationsTable, viewsData, 
                                     blocksOrder, predicateTypes,
                                     answersToStore, printVariables)
    
    #Check that the output directory exists
    path = os.path.normpath(output_directory + '/Solver_C_code')
    include_path = os.path.normpath(path + '/include')
    if os.path.exists(path):
        shutil.rmtree(path)
    
    os.makedirs(path)
    os.makedirs(include_path)
    
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
        
    