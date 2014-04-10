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
    
    for value in xrange(min_length, max_length+1):
        ints = ['int' for _ in xrange(value+1)]
        outfile.write('extern void Ds_insert_{}({});\n'.format(str(value), ', '.join(ints)))
        
    outfile.write('\n')
            
    ints = ['int', 'int']
    for p in xrange(max_length-1):
        outfile.write('extern intList * Ds_get_intList_{}({});\n'.format(str(p+1), ', '.join(ints)))
        ints.append('int')
        
def fillDataStructureSolutionHeaderFunctions(outfile):
    for answer in GenerationData.answersToStore:
        length = getPredicateLength(answer)
        ints = ['int' for _ in xrange(length)]
         
        outfile.write('extern int  Ds_contains_solution_{}({});\n'.format(answer, ', '.join(ints)))
        outfile.write('extern void Ds_append_solution_{}({});\n'.format(answer, ', '.join(ints)))
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
    data = []
    for rule in GenerationData.equationsTable:
        data.append((rule.leftSideName, 
                     len(rule.leftSideCons)))
        data.append((rule.rightSideName, 
                     len(rule.rightSideCons)))

    # Remove duplicates
    data = set(data)
    
    i = 0
    for pred_name, length in data:
        if i == 0:
            conditional = 'if'
        else:
            conditional = 'else if'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['b->VAR_' + str(x) for x in xrange(1, length+1)])
        
        outfile.write('\t{} (b->PREDICATE == {})\n'.format(conditional, pred_name))
        outfile.write('\t\tfprintf(file, "X_{}({}).", {});\n'.format(pred_name, formatting, variables))
        i += 1
        
def fillPrintAnswer(outfile):
    data = []
    for rule in GenerationData.equationsTable:
        data.append((rule.leftSideName, 
                     len(rule.leftSideCons)))
        data.append((rule.rightSideName, 
                     len(rule.rightSideCons)))

    # Remove duplicates
    data = set(data)
    
    i = 0
    for pred_name, length in data:
        if i == 0:
            conditional = 'if'
        else:
            conditional = 'else if'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['b->VAR_' + str(x) for x in xrange(1, length+1)])
        
        outfile.write('\t{} (b->PREDICATE == {})\n'.format(conditional, pred_name))
        outfile.write('\t\tfprintf(file, "{}({}).\\n", {});\n'.format(pred_name, formatting, variables))
        i += 1

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
    def printtemp(tabs):
        # Do we have to store the answer??
        if rule.rightSideName in answersToStore:
            pred = rule.rightSideName

            if rule.type == 2:
                tabs += '\t' * sum(((lambda x: 1 if isinstance(x, str) else 0)(x) 
                                        for x in rule.consultingValues))
                                
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

        outfile.write('\t\tif (current->b.PREDICATE == {})'.format(predicate ))
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
        outfile.write('#endif\n')
                
        tabs = '\t\t\t'
        for rule in rules:
            if rule.type == 1:
                # Do we have equal cards? If so we need to be sure they match before process the variable 
                do_we_have_equal_cards = (len(set(rule.leftSideCons)) != len(rule.leftSideCons))
                if do_we_have_equal_cards:
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
                        outfile.write('){\n')
                        tabs += '\t'
                        
                outfile.write('{}VAR.PREDICATE = {};\n'.format(tabs, rule.rightSideName))
                for pos, answer_pos in enumerate(rule.rightSideCons, 1):
                    outfile.write('{}VAR.VAR_{} = current->b.VAR_{};\n'.format(tabs,
                                                                               str(pos),
                                                                               str(answer_pos)))
                    
                printtemp(tabs)
                
                if do_we_have_equal_cards:
                    tabs = tabs[:-1]
                    outfile.write('{}}}\n'.format(tabs, tabs))
                    
            if rule.type == 2:
                left_pred_len = len(rule.leftSideCons)
                commonVars_len = len(rule.common_vars)
                
                do_we_have_equal_cards_var = (len(set(rule.leftSideCons)) != len(rule.leftSideCons))
                if do_we_have_equal_cards_var:
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
                    outfile.write('){\n')
                    tabs += '\t'
                
                args_common = ', '.join(['current->b.VAR_{}'.format(str(x[1])) for x in rule.common_vars])
                
                if commonVars_len == 0:
                    outfile.write('{}Ds_get_intValues_Level0_init();\n'.format(tabs))
                    outfile.write('{}while(Ds_get_intValues_Level0(&t0)){{\n'.format(tabs))                    
                else:
                    outfile.write('{}t1 = Ds_get_intList_{}({}, {});\n'
                              .format(tabs,
                                      commonVars_len,
                                      aliasToViewNames[rule.aliasName],
                                      args_common))
                    
                    outfile.write('{}for (; t1; t1 = t1->next){{\n'.format(tabs))
                    
                for x in xrange(commonVars_len+1, len(rule.consultingValues)):
                    if commonVars_len == 0:
                        args = 't0'
                        if x > 1: args += ', '
                        tabs = tabs + '\t' * x
                    else:
                        args = args_common + ', '
                        tabs = tabs + '\t' * (x - 1)
                        
                    args += ', '.join(['t{}->value'.format(str(i))
                                       for i in xrange(1, x)])
                    outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                                  .format(tabs, x, x,
                                          aliasToViewNames[rule.aliasName],
                                          args))
                    outfile.write('{}for (; t{}; t{} = t{}->next)'.format(tabs,
                                                                          x, x, x))
                    outfile.write('{\n')
                
                if do_we_have_equal_cards_var:
                    tabs = '\t\t\t\t'
                else:
                    tabs = '\t\t\t'
                tabs += '\t' * sum(((lambda x: 1 if isinstance(x, str) else 0)(x) 
                                        for x in rule.consultingValues))
                
                outfile.write('{}VAR.PREDICATE = {};\n'.format(tabs,
                                                               rule.rightSideName))
                
                do_we_have_equal_cards_query = (len(set(rule.consultingValues)) != len(rule.consultingValues))
                if do_we_have_equal_cards_query:
                    temp_dict = defaultdict(list)
                    first_var_position = 0
                    for rule_pos, var_name in enumerate(rule.consultingValues, 1):
                        if type(var_name) == int:
                            first_var_position += 1 
                        temp_dict[var_name].append(rule_pos - first_var_position)
                            
                    lists_of_duplicated_vars = filter(lambda x: len(x) > 1, temp_dict.values())
                    outfile.write('{}if('.format(tabs))
                    for pos, l in enumerate(lists_of_duplicated_vars):
                        t = ['t{}->value'.format(x) for x in l]
                        outfile.write('{}'.format(' == '.join(t)))
                        if pos != len(lists_of_duplicated_vars)-1:
                            outfile.write(' &&\n{}   '.format(tabs))
                    outfile.write('){\n')
                    tabs += '\t'
                
                for pos, var in enumerate(rule.rightSideCons, start=1):
                    outfile.write('{}VAR.VAR_{} = '.format(tabs, pos))
                    if isinstance(var, str):
                        t_index = rule.consultingValues.index(var) + 1\
                                   - commonVars_len
                        if commonVars_len == 0:
                            if t_index == 1:
                                outfile.write('t0;\n')
                            else:
                                outfile.write('t{}->value;\n'.format(str(t_index-1)))
                        else:
                            outfile.write('t{}->value;\n'.format(str(t_index)))
                    else:
                        outfile.write('current->b.VAR_{};\n'.format(str(var)))
                
                if do_we_have_equal_cards_query:
                    printtemp(tabs[:-2])
                else:
                    printtemp(tabs[:-1])
                
                if do_we_have_equal_cards_var:
                    tabs = tabs[:-1]
                    outfile.write('{}}}\n'.format(tabs, tabs))
                    
                if do_we_have_equal_cards_query:
                    tabs = tabs[:-1]
                    outfile.write('{}}}\n'.format(tabs, tabs))
                
                for x in xrange(commonVars_len+1, len(rule.consultingValues)):
                    tabs = tabs[:-1]
                    outfile.write('{}'.format(tabs))
                    outfile.write('}\n')
                    
                outfile.write('\t\t\t}\n\n')
        
        if rule.type == 2 and predsToViewNames[predicate]:
            outfile.write('\n#ifdef NDEBUG\n')
            
            for view in predsToViewNames[rule.leftSideName]:
                args = ', '.join('current->b.VAR_{}'.format(x) for 
                            x in viewNamesToCombinations[view])
                formatting = ', '.join(('%i' for _ in viewNamesToCombinations[view]))
                
                outfile.write('\t\tfprintf(stderr, "\\tData structure: ')
                outfile.write('Adding {}({})\\n", {});\n'.format(view,
                                                                formatting,
                                                                args)) 
            
            outfile.write('#endif\n')
                    
            for view in predsToViewNames[predicate]:
                args = ', '.join('current->b.VAR_{}'.format(x) for 
                            x in viewNamesToCombinations[view])
                
                outfile.write('\t\t\tDs_insert_{}({}, {});\n'.format(left_pred_len,
                                                                       view,
                                                                       args))
                
        outfile.write('\t\t}\n\n')
        
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
    # answers. That value is the number of consulting values in a rule minus 
    # the number of common variables 
    length = max(len(x.consultingValues) - len(x.common_vars) for x in equationsTable if x.type == 2)
    
    # In case there is a rule with no common variables
    if requires_t0:
        outfile.write('\tint t0;\n')
        
        # Check if the length of the comes from a rule with no common variables
        # in that case we have to subtract 1 to the value as we are already 
        # using t0. 
        no_cvars_max_length = max(len(x.consultingValues) for x in equationsTable
                                  if x.type == 2 and len(x.common_vars) == 0)
        if no_cvars_max_length == length:
            length -= 1
            
    args = ', '.join(['*t{}'.format(str(x+1)) for x in xrange(length)])
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
        for pred in lengthToPreds[length]:
            if pred in answersToStore:
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
    # Here we emit code to deal with the views. The length of the views is the same of the
    # length of the predicate it represents. Views can only exist for predicates on the 
    # right side of the rules so we take the minimum and maximum lengths of the predicates
    # of right side of the rules and emit functions for those values and the values in between
    min_length = min(chain((len(x.leftSideCons) for x in GenerationData.equationsTable if x.type == 2)))
    max_length = max(chain((len(x.leftSideCons) for x in GenerationData.equationsTable if x.type == 2)))
    
    #for length in xrange(2, max_pred_len+1):
    for length in xrange(min_length, max_length+1):
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
    answersToStore = GenerationData.answersToStore
    
    for answer in answersToStore:
        # Get the length of the predicate
        length = getPredicateLength(answer)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('int Ds_contains_solution_{}({})'.format(answer,
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
                                                           answer)
        else:
            node = 'R{}'.format(answer)
        outfile.write('{}return Judy1Test({}, x_{}, PJE0);\n'.format(tabs, node,
                                                                   length))
        
        outfile.write('}\n\n')
        
def fillDataStructureAppendSolutionFunctions(outfile):
    answersToStore = GenerationData.answersToStore
    
    for answer in answersToStore:
        # Get the length of the predicate
        length = getPredicateLength(answer)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('void Ds_append_solution_{}({})'.format(answer,
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
                                                           answer)
        else:
            node = 'R{}'.format(answer)
        
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
    
    lengths = list(xrange(getQueryMinimumLength(), getQueryMaximumLength()+1))
    
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

    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    # This checks that we don't handle level 1 nodes as for the current generation model doesn't 
    # contemplate the possibility of having a level 1 node.
    #if min_value == 1: min_value += 1
    #lengths = xrange(min_value, max_value + 1)
    lengths = xrange(2, number_of_data_structure_nodes + 1)
    
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
        
        outfile.write('}\n\n')

# As the level 0 is currently handled outside the level nodes this is necessary to store
# the answers formed by only one predicate
def fillDataStructureRootAnswers(outfile):
    answers_of_length_1 = set()
    for rule in GenerationData.equationsTable:
        if len(rule.rightSideCons) == 1:
            answers_of_length_1.add(rule.rightSideName)
            
    if answers_of_length_1:
        line = ', '.join(['R{}'.format(answer) for answer in answers_of_length_1])
        outfile.write('static Pvoid_t {};\n'.format(line))
        
# This function only should be executed if there are predicates of length 2
# If we only have type 1 rules we don't have level 2 nodes so this will
# cause an error
@check_for_predicates_of_type2        
def fillDataStructureLevel2Line(outfile):
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
     'fill_DsRootAnswers'        : fillDataStructureRootAnswers,
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
        
    