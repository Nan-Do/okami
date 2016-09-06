'''
Created on Aug 21, 2013

@author: nando
'''

import os
import shutil
import sys

from collections import namedtuple, defaultdict
from operator import attrgetter
from itertools import count, chain
from datetime import datetime
from functools import wraps
from Types import Argument, ArithmeticExpression

# Settings for the parser
DELIMITER = '%%'
SOURCE_DIRECTORY = "C_Template"
#OUTPUT_DIRECTORY = "./"

INCLUDE_FILES = ['utils.h', 'solver.h', 'data_structure.h', 
                 'data_structure_common.h', 'fact.h', 'parser.h',
                 'solver_queue.h']

SOURCE_FILES = ['makefile', 'main.c', 'parser.c',
                'data_structure_common.c', 'solver.c', 
                'data_structure.c', 'solver_queue.c']

EMPTY_LINE = '\n'
SPACES = ' ' * 4

# Global data for the module
GenerationData = None

# Utility functions

# This function returns an iterator to a list containing all the extensional predicates
# The extensional predicates are stored in the block1 of every stratum. 
def getExtensionalPredicates():
    return chain(*map(attrgetter('block1'), map(attrgetter('ordering'), GenerationData.stratums)))

# This function returns an itertaror to all the equations contained in the stratums
def getEquationsFromAllStratums():
    return chain(*map(attrgetter('equations'), GenerationData.stratums))

# This function returns an itertaror to all the views contained in the stratums
def getViewsFromAllStratums():
    return map(attrgetter('views'), GenerationData.stratums)

# Utility functions
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

# In order to get the minimum node and the maximum node we have to check the right side
# of every rule to store the answers and the left side of the rule of type 2
def getDataStructureNodesMaximumLength():
    return  max(chain([len(x.leftArguments) for x in getEquationsFromAllStratums() if x.type == 2],
                      [len(x.rightArguments) for x in getEquationsFromAllStratums()]))

# This is a closure to check if we have predicates of type 2, some functions
# like the ones handling the requests to the data structures should not be 
# executed if we don't have predicates of type 2 in the source datalog program.
# Instead of checking that behavior explicitly in the destiny functions 
# this behavior has been extracted as a decorator.
def check_for_predicates_of_type2(view_func):
    def _decorator(request, *args, **kwargs):
        response = None
        # Make sure we don't call the function if we don't have predicates of type 2
        if len([x for x in getEquationsFromAllStratums() if x.type == 2]):
            response = view_func(request, *args, **kwargs)
        return response
    return wraps(view_func)(_decorator)

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

# This function returns the Answers of length 1.
# An answer of length 1 is:
#    A predicate on the body of a rule with length 1.
#    A predicate on the head of a rule with length 1.
#    A negated predicate of length 1
def getAnswersOfLength_1():
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
                
    return (answers_of_length_1, predicates_in_rules_of_length_1) 


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

# This function returns all the identifiers for the identifiers we have to query
# on the database.
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

# utils.h
def fillProgramName(outfile):
    outfile.write('#define PROGRAM_NAME "{}"'.format('solver'))
    
def fillHypothesis(outfile):
    hypothesis = set(eq.leftVariable.id.uniqueId for eq in getEquationsFromAllStratums())
    hypothesis |= set(eq.rightVariable.id.uniqueId for eq in getEquationsFromAllStratums())
    hypothesis |= set(negated_element.id.uniqueId 
                            for eq in getEquationsFromAllStratums()
                            for negated_element in eq.negatedElements)
    outfile.write('/* Hypotheses */\n')
    for position, hypothesis in enumerate(hypothesis):
        line = '#define {}\t{}\n'.format(hypothesis, str(position))
        outfile.write(line)
    
def fillAccessViews(outfile):
    #sorted_views = GenerationData.viewsData.viewsOrdering
    sorted_views = [ view.viewsOrdering for view in getViewsFromAllStratums() ]
    outfile.write('/* View prefixes */\n')

    for view_name, view_position in chain(*sorted_views):
        line = '#define {}\t{}\n'.format(view_name, str(view_position))
        outfile.write(line)
        
# solver.h
def fillRewritingVariable(outfile):
    outfile.write('\tunsigned char PREDICATE;\n\n')
    
    max_length = max(chain((len(x.leftArguments) for x in getEquationsFromAllStratums()), 
                           (len(x.rightArguments) for x in getEquationsFromAllStratums())))
    for p in xrange(1, max_length+1):
        outfile.write('\tunsigned int VAR_{};\n'.format(str(p)))
        
# data_structure.h
@check_for_predicates_of_type2
def fillDataStructureQueryHeaderFunctions(outfile):
    def get_successors_structure_name():
        if GenerationData.compositionStructures['Successors'] == 'Stack': return 'uIntListStackNodePtr'
        elif GenerationData.compositionStructures['Successors'] == 'Queue': return 'uIntArrayQueuePtr'
        else: return 'UNKNOWN'
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
        outfile.write('extern {} Ds_get_intList_{}({});\n'.format(get_successors_structure_name(),
                                                                  str(p+1),
                                                                  ', '.join(ints)))
        ints.append('int')
        
def fillDataStructureSolutionHeaderFunctions(outfile):
    for variable_id in getAllSolutions():
        length = getPredicateLength(variable_id)

        ints = ['int' for _ in xrange(length)]
         
        outfile.write('extern int  Ds_contains_solution_{}({});\n'.format(variable_id.name,
                                                                          ', '.join(ints)))
        outfile.write('extern void Ds_append_solution_{}({});\n'.format(variable_id.name,
                                                                        ', '.join(ints)))
    outfile.write('\n')

# solver.c
def fillInputTuplesFiles(outfile):
    spaces_level_1 = SPACES
    extensional = list(getExtensionalPredicates())
    
    outfile.write('static char *tuples_input_files[] = {\n')
    for pos, (pred_name, _) in enumerate(extensional):
        if pos != len(extensional)-1:
            outfile.write('{}"{}.tuples",\n'.format(spaces_level_1,
                                                    pred_name))
        else:
            outfile.write('{}"{}.tuples"\n'.format(spaces_level_1,
                                                   pred_name))
    outfile.write('};\n')
    outfile.write('#define INPUT_TUPLES_FILES {}\n'.format(len(extensional)))
    
def fillOutputTuplesFiles(outfile):
    spaces_level_1 = SPACES
    outputTuples = GenerationData.answersToStore
    
    outfile.write('static char *tuples_output_files[] = {\n')
    for pos, (pred_name, _) in enumerate(outputTuples):
        if pos != len(outputTuples)-1:
            outfile.write('{}"{}.tuples",\n'.format(spaces_level_1,
                                                    pred_name))
        else:
            outfile.write('{}"{}.tuples"\n'.format(spaces_level_1,
                                                   pred_name))
    outfile.write('};\n')
    outfile.write('#define OUTPUT_TUPLES_FILES {}\n'.format(len(outputTuples)))
    
    outfile.write('FILE')
    for pos, (pred_name, _) in enumerate(outputTuples):
        outfile.write(' *fp_{}'.format(pred_name))
        if pos != len(outputTuples) - 1:
            outfile.write(',')
    outfile.write(';\n')
    
def fillPrintRewritingVariable(outfile):
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2

    for position, ((pred_name, pred_uniqueId), length) in enumerate(getAllPredicatesLengths()):
        if position == 0:
            conditional = 'if'
        else:
            conditional = 'else if'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['b->VAR_' + str(x) for x in xrange(1, length+1)])
        
        outfile.write('{}{} (b->PREDICATE == {})\n'.format(spaces_level_1,
                                                           conditional,
                                                           pred_uniqueId))
        outfile.write('{}fprintf(file, "X_{}({}).", {});\n'.format(spaces_level_2,
                                                                   pred_name,
                                                                   formatting,
                                                                   variables))
        
def fillPrintAnswer(outfile):
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2

    for position, ((pred_name, pred_uniqueId), length) in enumerate(getAllPredicatesLengths()):
        if position == 0:
            conditional = 'if'
        else:
            conditional = 'else if'
        
        formatting = ', '.join(['%i' for x in xrange(length)])
        variables = ', '.join(['b->VAR_' + str(x) for x in xrange(1, length+1)])
        
        outfile.write('{}{} (b->PREDICATE == {})\n'.format(spaces_level_1,
                                                           conditional,
                                                           pred_uniqueId))
        outfile.write('{}fprintf(file, "{}({}).\\n", {});\n'.format(spaces_level_2,
                                                                    pred_name,
                                                                    formatting,
                                                                    variables))


def fillSolverInit(outfile):
    spaces_level_1 = SPACES

    # First init the queues
    number_of_stratums = len(GenerationData.stratums)
    outputTuples = GenerationData.answersToStore
    
    for queue_number in xrange(1, number_of_stratums + 1):
        outfile.write('{}SolverQueue_init(&solver_queue{});\n'.format(spaces_level_1,
                                                                      queue_number))
        
    outfile.write('\n')
        
    for pos, predicate in enumerate(outputTuples):
        outfile.write('{}fp_{} = fopen(tuples_output_files[{}], "w+");\n'.format(spaces_level_1,
                                                                                 predicate[0],
                                                                                 str(pos)))
        
def fillStratumQueueInitializers(outfile):
    extensional = list(getExtensionalPredicates())
    extensional_as_set = set(extensional)
    idToStratumLevels = GenerationData.idToStratumLevels
    number_of_stratums = len(GenerationData.stratums)
    
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    spaces_level_4 = SPACES * 4

    # Create a new dictionary from idToStratumLevels only containing
    # extensional predicates
    extensionalToStratumLevels = {k: v for (k,v) in idToStratumLevels.iteritems() if k in extensional_as_set}
    
    for stratum_level in xrange(1, number_of_stratums + 1):
        outfile.write('int solver_init_stratum_level{}(){{\n'.format(str(stratum_level)))
        outfile.write('{}FILE *fp;\n'.format(spaces_level_1))
        outfile.write('{}Fact fact;\n'.format(spaces_level_1))
        outfile.write('{}TYPE_REWRITING_VARIABLE VAR;\n\n'.format(spaces_level_1))
        
        outfile.write('#ifdef NDEBUG\n')
        outfile.write('{}fprintf(stderr, "STRATUM LEVEL: {}\\n");\n'.format(spaces_level_1,
                                                                            str(stratum_level)))
        outfile.write('#endif\n\n')
        
        # Get the predicates that belong to the current stratum level
        idsVars = (idVar for (idVar, levels) in extensionalToStratumLevels.iteritems()
                                if stratum_level in levels)
        
        # If we are in the first of the level we must honor the order of the block
        # as negated predicates must be put first
        if (stratum_level == 1):
            idsVarsSet = set(idsVars)
            idsVars = ( x for x in extensional if x in idsVarsSet )
            
        for idVar in idsVars:
            pos = extensional.index(idVar)
            
            length = getPredicateLength(idVar)
        
            outfile.write('{}fp = fopen(tuples_input_files[{}], "r");\n'.format(spaces_level_1,
                                                                                pos))
            outfile.write('{}if (!fp){{\n'.format(spaces_level_1))
            outfile.write('{}fprintf(stderr, "Error: Can\'t open file %s\\n",'.format(spaces_level_2))
            outfile.write(' tuples_input_files[{}]);\n'.format(pos))
            outfile.write('{}return false;\n'.format(spaces_level_2))
            outfile.write('{}}}\n'.format(spaces_level_1))
            outfile.write('{}while (parser_get_fact(fp, NULL, &fact) == 1){{\n'.format(spaces_level_1))
            outfile.write('{}VAR.PREDICATE = {};\n'.format(spaces_level_2,
                                                           idVar.uniqueId))
            
            for x in xrange(length):
                outfile.write('{}VAR.VAR_{} = fact.values[{}];\n'.format(spaces_level_2,
                                                                         str(x+1), x))
    
            outfile.write('\n')
            
            formatting = ','.join(['%i' for x in xrange(length)])
            outfile.write('#ifdef NDEBUG\n')
            outfile.write('{}fprintf(stderr, "Adding rewriting variable: X_{}'.format(spaces_level_2,
                                                                                      idVar.name))
            outfile.write('({})\\n",\n'.format(formatting))
            
            for x in xrange(length):
                if x != (length - 1):
                    outfile.write('{}VAR.VAR_{},\n'.format(spaces_level_4,
                                                           str(x+1)))
                else:
                    outfile.write('{}VAR.VAR_{});\n'.format(spaces_level_4,
                                                            str(x+1)))
            outfile.write('#endif\n\n')
            
            outfile.write('{}SolverQueue_append(&solver_queue{}, &VAR);\n'.format(spaces_level_2,
                                                                                  str(stratum_level)))
            outfile.write('{}}}\n'.format(spaces_level_1))
            outfile.write('{}fclose(fp);\n\n'.format(spaces_level_1))
        
        outfile.write('{}return true;\n'.format(spaces_level_1))
        outfile.write('}\n\n')
    
def fillSolverCompute(outfile):
    # This function is used to obtain the index position of the querying argument.
    # The position of the argument has on the query to the database.
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
                if GenerationData.compositionStructures['Successors'] == 'Stack':
                    emitting_code += "t{}->value".format(t_index-1)
                elif GenerationData.compositionStructures['Successors'] == 'Queue':
                    emitting_code += "t{0}->values[c{0}]".format(t_index-1)
        else:
            if GenerationData.compositionStructures['Successors'] == 'Stack':
                emitting_code += "t{}->value".format(t_index)
            elif GenerationData.compositionStructures['Successors'] == 'Queue':
                    emitting_code += "t{0}->values[c{0}]".format(t_index)
            
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
            return "current->b.VAR_{}".format(expression)
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
                    emitting_code += "current->b.VAR_{}".format(args[x])
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
    #  spaces -> A string. Represents the number of spaces that we have to print when emitting code.
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

            args = ', '.join('VAR.VAR_{}'.format(x) for 
                            x in xrange(1, len(equation.rightArguments)+1))
            
            outfile.write('\n{}if (!Ds_contains_solution_{}({})'.format(spaces,
                                                                        variable_id.name,
                                                                        args))
            
            if equation.booleanExpressions:
                outfile.write( ' &&\n{0}{1}/* Boolean expression conditions */\n{0}{1}'.format(spaces,
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
                        boolean_expressions_str += " &&\n{}{}".format(spaces,
                                                                      '    ')
                        
                outfile.write(boolean_expressions_str)
            
            if equation.negatedElements:
                outfile.write( ' && \n{0}{1}/* Negated predicates */'.format(spaces,
                                                                             '    '))
            
            for (pos, negated_element) in enumerate(equation.negatedElements):
                negated_arguments_str = []

                for negated_arg in negated_element.arguments:
                    if negated_arg.type == 'constant':
                        negated_arguments_str.append(str(negated_arg.value))
                    else:
                        found = False
                        for argument, position in equation.leftArguments:
                            if negated_arg == argument:
                                negated_arguments_str.append('current->b.VAR_{}'.format(position))
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
                outfile.write('\n{}{}!Ds_contains_solution_{}({})'.format(spaces,
                                                                          '    ',
                                                                          negated_element.id.name,
                                                                          negated_arguments))
                if (pos != len(equation.negatedElements) - 1):
                    outfile.write(' &&')
            spaces += SPACES
            outfile.write('){\n')
            outfile.write('#ifdef NDEBUG\n')
            # Print the variable information
            outfile.write('{}fprintf(stderr, "\\tAdding variable -> ");\n'.format(spaces))
            outfile.write('{}print_rewriting_variable(stderr, &VAR);\n'.format(spaces))
            outfile.write('{}fprintf(stderr, "\\n");\n'.format(spaces))
            # Print the levels in which the variable is going to be added. Here is printed for
            # debugging purposes.
            for level in idToStratumLevels[variable_id]:
                outfile.write('{}fprintf(stderr, "\\t  Queue {}\\n");\n'.format(spaces, str(level)))
            outfile.write('#endif\n\n')
            
            # To compute a program a variable can be required to be evaluated in different queues, here we
            # make sure that the variable is added to every required queue. IdToStratums is a dictionary that
            # contains the required information to emit the code. It takes as a key a variable_id and returns
            # the queue levels in which is required.
            for queue_level in idToStratumLevels[variable_id]:
                outfile.write('{}SolverQueue_append(&solver_queue{}, &VAR);\n'.format(spaces, str(queue_level)))
            outfile.write('{}Ds_append_solution_{}({});\n'.format(spaces,
                                                                  variable_id.name,
                                                                  args))
            spaces = spaces[:-len(SPACES)]
            outfile.write('{}'.format(spaces))
            outfile.write('}\n')
        else:
            outfile.write('{}SolverQueue_append(&solver_queue1, &VAR);\n'.format(spaces))
            
    #equationsTable = GenerationData.equationsTable
    #predsToViewNames = GenerationData.viewsData.predsToViewNames
    predsToViewNames = dict(chain(*[ view.predsToViewNames.items() for view in getViewsFromAllStratums() ]))
    #viewNamesToCombinations = GenerationData.viewsData.viewNamesToCombinations
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    #aliasToViewNames = GenerationData.viewsData.aliasToViewNames
    aliasToViewNames = dict(chain(*[ view.aliasToViewNames.items() for view in getViewsFromAllStratums() ]))
    answersToStore = GenerationData.answersToStore
    printVariables = GenerationData.printVariables
    outputTuples = GenerationData.answersToStore
    idToStratumLevels = GenerationData.idToStratumLevels
    
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    spaces_level_3 = SPACES * 3
    spaces_level_5 = SPACES * 5

    # Here we emit code to handle the different stratums in the solver_compute function
    for level, stratum in enumerate(GenerationData.stratums, start=1):
        outfile.write('{}/*Stratum {}*/\n'.format(spaces_level_1,
                                                  level))
        outfile.write('{}solver_init_stratum_level{}();\n'.format(spaces_level_1,
                                                                  str(level)))
        outfile.write('{}while (solver_queue{}.head){{\n'.format(spaces_level_1,
                                                                 str(level)))
        outfile.write('{}current = solver_queue{}.head;\n\n'.format(spaces_level_2,
                                                                    str(level)))
        
        block1 = stratum.ordering.block1
        block2 = stratum.ordering.block2
        block3 = stratum.ordering.block3
    
        for variable_id in chain(block1, block2, block3):
            # Get the equation of the predicate raise an exception if not found
            equations = (x for x in getEquationsFromAllStratums() if x.leftVariable.id == variable_id)
    
            outfile.write('{}if (current->b.PREDICATE == {})'.format(spaces_level_2,
                                                                     variable_id.uniqueId))
            outfile.write('{\n')

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
                outfile.write("{}print_answer(stdout, &current->b);\n".format(spaces_level_3))
                
            # Is it a solution? Then print it to a file.
            if level == level_to_store_answer and variable_id in outputTuples:
                outfile.write("{}print_answer(fp_{}, &current->b);\n".format(spaces_level_3,
                                                                             variable_id.name))
            
            # Debug information
            pred_length = getPredicateLength(variable_id)
            outfile.write('#ifdef NDEBUG\n')
            formatting = ', '.join(['%i' for _ in xrange(pred_length)])
            separator = ',\n{}'.format(spaces_level_5)
            args = separator.join(('current->b.VAR_{}'.format(str(x+1)) for x in xrange(pred_length)))
            output_string = '{}fprintf(stderr, "Handling rewriting '.format(spaces_level_3) +\
                            'variable: X_{}'.format(variable_id.name) +\
                            '({})\\n",\n{}{});\n'.format(formatting,
                                                         spaces_level_5,
                                                         args)
            outfile.write(output_string)
            #outfile.write('#endif\n')
            
            # Here we emit code to add data to the data structure if we are in a type 2 equation.
            # Again we only store the variable to the database if we are in the first level (stratum)
            # the variable appears in.
            # We emit debugging code via a c macro to check what is going to be added
            # to the data structure. We show the view and the values being added.
            # After we use the appropriate call to add the solution to the data structure
            if variable_id in predsToViewNames:
                # This is the debugging part
                #outfile.write('\n#ifdef NDEBUG\n')
                  
                # Debug information: If the predicate has length 1 the it becomes a solution and has to be
                # treated as such. Otherwise we insert a value into the list as normal
                if (level == level_to_store_answer) and (pred_length == 1):
                    outfile.write('{}fprintf(stderr, "\\tData structure: '.format(spaces_level_3))
                    outfile.write('Adding solution {}(%i)\\n", current->b.VAR_1);\n'.format(variable_id.name))
                elif (level == level_to_store_answer):
                    for view in predsToViewNames[variable_id]:
                        args = ', '.join('current->b.VAR_{}'.format(x) for
                                         x in viewNamesToCombinations[view])
                        formatting = ', '.join(('%i' for _ in viewNamesToCombinations[view]))
      
                        outfile.write('{}fprintf(stderr, "\\tData structure: '.format(spaces_level_3))
                        outfile.write('Adding {}({})\\n", {});\n'.format(view,
                                                                        formatting,
                                                                        args))
              
            # This marks the end of the debug information macro this line has to be always emitted as 
            # the portion of the handling the rewriting variable is always emitted and only the
            # adding solution is optional if the predicate is part of a type 2 equation that is there is     
            # a view associated with it
            outfile.write('#endif\n')
            
            # Unfortunately because of the problem of the previous line we have to recheck here if the
            # predicate has a view associated with it
            if variable_id in predsToViewNames:     
                # This is part in which we add the solution to the data structure. If the predicate has length
                # 1 we have to add directly the solution, as by convention there is no level node of length 0
                # and the predicates of length 1 are turned into solutions
                if (level == level_to_store_answer) and (pred_length == 1):
                    outfile.write('{}Ds_append_solution_{}(current->b.VAR_1);\n'.format(spaces_level_3,
                                                                                        variable_id.name))
                    # If the variable only appears as a negated predicate we don't have to insert it to the database
                    if variable_id in getAllConsultingPredicates():
                        outfile.write('{}Ds_insert_1(current->b.VAR_1);\n\n'.format(spaces_level_3))
                elif (level == level_to_store_answer):
                    for view in predsToViewNames[variable_id]:
                        args = ', '.join('current->b.VAR_{}'.format(x) for
                                         x in viewNamesToCombinations[view])
                        
                        # If the identifier pertains to the solutions we have to append it as a solution
                        # to the database. Checking the getAllSolutions function to know what it is considered
                        # to be a solution will raise an error on the evaluation of some programs due to equal
                        # cards.
                        if variable_id in getPredicatesWithAllVariablesBeingInTheSharedSet() |\
                                          getPredicatesWithAllVariablesBeingInTheSharedSetIncludingConstants()|\
                                          getNegatedPredicates():
                            outfile.write('{}Ds_append_solution_{}({});\n'.format(spaces_level_3,
                                                                                  variable_id.name,
                                                                                  args))
                        
                        # We have to update the database if the identifier pertains to a variable
                        # that is going to be consulted in the database. That means it pertains to
                        # an equation  
                        if variable_id in getAllConsultingPredicates():
                            outfile.write('{}Ds_insert_{}({}, {});\n'.format(spaces_level_3,
                                                                             pred_length,
                                                                             view,
                                                                             args))
                        outfile.write('\n')
            
                    
            spaces = spaces_level_3
            for equation_number, equation in enumerate(equations, start=1):
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
                        
                        outfile.write('{}if ('.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            t = ['current->b.VAR_{}'.format(x) for x in l]
                            outfile.write('{}'.format(' == '.join(t)))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' &&\n{}   '.format(spaces))
                    if argument_constants_left_side:
                        if have_equal_cards:
                            outfile.write(' &&\n{}   '.format(spaces))
                        else:
                            outfile.write('{}if ('.format(spaces))
                            
                        for pos, elem in enumerate(argument_constants_left_side):
                            outfile.write('current->b.VAR_{} == {}'.format(elem[1], 
                                                                           str(elem[0].value)))
                            if pos != len(argument_constants_left_side)-1:
                                outfile.write(' &&\n{}   '.format(spaces))
                            
                    if have_equal_cards or argument_constants_left_side:
                        outfile.write('){\n')
                        spaces += SPACES
                            
                    outfile.write('{}VAR.PREDICATE = {};\n'.format(spaces, equation.rightVariable.id.uniqueId))
                    for pos, answer in enumerate(equation.rightArguments, 1):
                        # Check if we are dealing with a constant propagated trough the datalog source code.
                        # If we have an integer here it means it is a rewriting constant propagated value
                        # otherwise it is a constant specified on the datalog source code.
                        # In this case we have a propagated position
                        code = compose_expression(answer, None, None)
                        outfile.write('{}VAR.VAR_{} = {};\n'.format(spaces,
                                                                    str(pos),
                                                                    code))
                        
                    common_block(spaces, equation, level, 
                                 len(GenerationData.stratums),
                                 idToStratumLevels)
                    
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
                        outfile.write('{}if('.format(spaces))

                        for pos, l in enumerate(lists_of_duplicated_vars):
                            t = ['current->b.VAR_{}'.format(x) for x in l]
                            outfile.write('{}'.format(' == '.join(t)))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' &&\n{}   '.format(spaces))
                        if argument_constants_left_side:
                            outfile.write(' &&\n{}   '.format(spaces))
                                                
                            for pos, elem in enumerate(argument_constants_left_side):
                                outfile.write('current->b.VAR_{} == {}'.format(elem[1], 
                                                                               str(elem[0].value)))
                                if pos != len(argument_constants_left_side)-1:
                                    outfile.write(' &&\n{}   '.format(spaces))
                                    
                        outfile.write('){\n')
                        spaces += SPACES

                        # Here we have to add the solution to the data structure if the predicate has all variables
                        # the same equal card. We check that if turning the list of leftArguments into a set the
                        # length is 1.
                        if len(set(equation.leftArguments)) == 1:
                            args = ['current->b.VAR_{}'.format(x) for x in l]
                            outfile.write("{}if (!Ds_contains_solution_{}({})){{\n".format(spaces,
                                                                                           equation.leftVariable.id.name,
                                                                                           ", ".join(args)))
                            spaces += SPACES
                            outfile.write("#ifdef NDEBUG\n")
                            outfile.write("{}fprintf(stderr, \"\\tAdding solution -> \");\n".format(spaces))
                            outfile.write("{}print_rewriting_variable(stderr, &current->b);\n".format(spaces))
                            outfile.write("{}fprintf(stderr, \"\\n\");\n".format(spaces))
                            outfile.write("#endif\n")
                            outfile.write("{}Ds_append_solution_{}({});\n".format(spaces,
                                                                                  equation.leftVariable.id.name,
                                                                                  ", ".join(args)))
                            spaces = spaces[:-len(SPACES)]
                            outfile.write("{}}}\n".format(spaces))
                    
                    elif argument_constants_left_side:
                        outfile.write('{}if('.format(spaces))
                        
                        for pos, elem in enumerate(argument_constants_left_side):
                            outfile.write('current->b.VAR_{} == {}'.format(elem[1],
                                                                           str(elem[0].value)))
                            if pos != len(argument_constants_left_side)-1:
                                outfile.write(' &&\n{}   '.format(spaces))
                                
                        outfile.write('){\n')
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
                        outfile.write('{}Ds_get_intValues_Level0_init();\n'.format(spaces))
                        outfile.write('{}while(Ds_get_intValues_Level0(&t0))'.format(spaces))
                        outfile.write('{\n')
                        spaces += SPACES
                        # If the length of the predicate is one we also have to make sure that the value we obtain
                        # is valid as we won't iterate to obtain more values
                        if len(equation.consultingArguments) == 1:
                            outfile.write('{}if (Ds_contains_solution_{}(t0))'.format(spaces,
                                                                                      equation.consultingPredicate.id.name))
                            outfile.write('{\n')
                    
                    else:
                        # We don't have equal cards in the set of common variables, we just iterate over the set
                        # emitting code appropriately. 
                        if not equal_cards_query_common_vars:
                            args_common = ', '.join(['current->b.VAR_{}'.format(str(x[1])) for x in equation.commonVariables])
                            #int_length = commonVars_len + len(argument_constants_consulting_values)
                            int_length = commonVars_len + len(argument_constants_consulting_values)
                        # Here we have equal cards in the set of common variables there fore we need to check which is 
                        # the real number of common variables in the query.
                        else:
                            # The number of common variables is just the number of integer values of the consulting values
                            # list
                            number_of_common_vars = sum(1 for x in equation.consultingArguments if isinstance(x, int))
                                                     
                            args_common = ', '.join(['current->b.VAR_{}'.format(str(x))
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
                            if equation_number > 1:
                                outfile.write(EMPTY_LINE)

                            # Here we just emit code for t1 using the computed values
                            outfile.write('{}t1 = Ds_get_intList_{}({}, {});\n'
                                          .format(spaces,
                                                  int_length,
                                                  aliasToViewNames[equation.aliasName],
                                                  args_common))
                            if GenerationData.compositionStructures['Successors'] == 'Queue':
                                outfile.write('{}for (c1 = 0; c1 < t1->last; c1++){{\n'.format(spaces))
                            elif GenerationData.compositionStructures['Successors'] == 'Stack':
                                outfile.write('{}for (; t1; t1 = t1->next){{\n'.format(spaces))
                            else:
                                raise KeyError
                        else:
                            outfile.write("{}if (Ds_contains_solution_{}({})){{\n".format(spaces,
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
                        if x > 1: spaces += SPACES
                        query_value = y + len(argument_constants_consulting_values)
                        if commonVars_len == 0:
                            args = 't0'
                            if x > 1: args += ', '
                        else:
                            args = args_common + ', '
                           
                        if not equal_cards_query_common_vars:
                            if GenerationData.compositionStructures['Successors'] == 'Stack':
                                args += ', '.join(['t{}->value'.format(i)
                                                for i in xrange(1, x)])
                            elif GenerationData.compositionStructures['Successors'] == 'Queue':
                                args += ', '.join(['t{0}->values[c{0}]'.format(i)
                                                for i in xrange(1, x)])
                            
                            outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                                          .format(spaces, x, query_value,
                                                  aliasToViewNames[equation.aliasName],
                                                  args))
                            #number_of_args = y + len(argument_constants_consulting_values)
                            #outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                            #              .format(spaces, x, number_of_args,
                            #                      aliasToViewNames[equation.aliasName],
                            #                      args))
                            if GenerationData.compositionStructures['Successors'] == 'Queue':
                                outfile.write('{0}for (c{1} = 0; c{1} < t{1}->last; c{1}++)'.format(spaces,
                                                                                                    str(x)))
                            elif GenerationData.compositionStructures['Successors'] == 'Stack':
                                outfile.write('{0}for (; t{1}; t{1} = t{1}->next)'.format(spaces,
                                                                                          str(x)))
                            else:
                                raise KeyError
                        else:
                            #outfile.write("X: {}\t\tARGS:{}\t\tNUMBER_OF_ARGS: {}\t\tY: {}\t\tCOMMON_VARS: {}\n".format(x, args, number_of_args, y, commonVars_len))
                            if GenerationData.compositionStructures['Successors'] == 'Queue':
                                args += ', '.join(['t{0}->values[c{0}]'.format(i)
                                                   for i in xrange(1, (y-commonVars_len)+1)])
                            elif GenerationData.compositionStructures['Successors'] == 'Stack':
                                args += ', '.join(['t{}->value'.format(i)
                                                   for i in xrange(1, (y-commonVars_len)+1)])
    
                            outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'.format(spaces,
                                                                                        (y-commonVars_len)+1,
                                                                                        query_value,
                                                                                        aliasToViewNames[equation.aliasName],
                                                                                        args))
                            #number_of_args = y + len(argument_constants_consulting_values)
                            #outfile.write('{}t{} = Ds_get_intList_{}({}, {});\n'
                            #              .format(spaces, (y-commonVars_len)+1, number_of_args,
                            #                      aliasToViewNames[equation.aliasName],
                            #                      args))
                            if GenerationData.compositionStructures['Successors'] == 'Queue':
                                outfile.write('{0}for (c{1} = 0; c{1} < t{1}->last; c{1}++)'.format(spaces,
                                                                                                    str((y-commonVars_len) + 1)))
                            elif GenerationData.compositionStructures['Successors'] == 'Stack':
                                outfile.write('{0}for (; t{1}; t{1} = t{1}->next)'.format(spaces,
                                                                                          str((y-commonVars_len) + 1)))
                            else:
                                raise KeyError
                                          
                        outfile.write('{\n')
                    
                    # This space emits code to start the new level of the source code after all the if's
                    # the code to indent the different ifs is emitted at previous enumerated for below
                    # the commonVars_len == 0 line
                    spaces += SPACES

                    outfile.write('{}VAR.PREDICATE = {};\n'.format(spaces,
                                                                   equation.rightVariable.id.uniqueId))
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
                        outfile.write('{}if('.format(spaces))
                        for pos, l in enumerate(lists_of_duplicated_vars):
                            if GenerationData.compositionStructures['Successors'] == 'Queue':
                                t = ['t{0}->values[c{0}]'.format(x) if (x > 0) else 't{}'.format(x) for x in l]
                            elif GenerationData.compositionStructures['Successors'] == 'Stack':
                                t = ['t{0}->value'.format(x) if (x > 0) else 't{}'.format(x) for x in l]

                            outfile.write('{}'.format(' == '.join(t)))
                            if pos != len(lists_of_duplicated_vars)-1:
                                outfile.write(' &&\n{}   '.format(spaces))
                        outfile.write('){\n')
                        spaces += SPACES
                    
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
                        outfile.write('{}VAR.VAR_{} = {};\n'.format(spaces,
                                                                    str(pos),
                                                                    code))
                                            
                    common_block(spaces, equation, level,
                                 len(GenerationData.stratums),
                                 idToStratumLevels)
                    
                    # Here we just emit source code to handle the indentation and the close every 
                    # required '}' character    
                    if equal_cards_rewriting_variable or argument_constants_left_side:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))
                        
                    if equal_cards_query_not_common_vars:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))
                        
                    if commonVars_len == 0 and len(equation.consultingArguments) == 1:
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}}}\n'.format(spaces))
                    
                    for x in xrange(commonVars_len+1, len(equation.consultingArguments) - len(argument_constants_consulting_values)):
                        spaces = spaces[:-len(SPACES)]
                        outfile.write('{}'.format(spaces))
                        outfile.write('}\n')

                    spaces = spaces_level_3
                    outfile.write('{}}}\n'.format(spaces))

            outfile.write('{}}}\n\n'.format(spaces_level_2))
        outfile.write('{0}solver_queue{1}.head = solver_queue{1}.head->next;\n'.format(spaces_level_2,
                                                                                       str(level)))
        outfile.write('{}free(current);\n'.format(spaces_level_2))
        outfile.write('{}}}\n'.format(spaces_level_1))
        
# In this function we emit code to close the file descriptors opened before
# to store the answers in files. The file descriptor is called fp_{} plus the
# name of the predicate.
def fillSolverFree(outfile):
    outputTuples = GenerationData.answersToStore
    number_of_stratums = len(GenerationData.stratums)
    
    spaces_level_1 = SPACES

    for predicate in outputTuples:
        outfile.write('{}fclose(fp_{});\n'.format(spaces_level_1,
                                                  predicate[0]))
        
    outfile.write('\n{}Ds_free();\n'.format(spaces_level_1))
    for queue_number in xrange(1, number_of_stratums+1):
        outfile.write('{}SolverQueue_free(&solver_queue{});\n'.format(spaces_level_1,
                                                                      queue_number))
    #outfile.write('{}Mem_free();\n'.format(spaces_level_1))

@check_for_predicates_of_type2
def fillIntList(outfile):
    #equationsTable = GenerationData.equationsTable
    spaces_level_1 = SPACES
    
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
        outfile.write('{}unsigned int t0;\n'.format(spaces_level_1))
        
        # Check if the longest length comes from a rule with no common variables
        # if that is the case then we have to subtract 1 to the value as we are already 
        # using t0. 
        no_cvars_max_length = max(len(filter(lambda y: isinstance(y, Argument) and y.type == 'variable', x.consultingArguments)) 
                                  for x in getEquationsFromAllStratums() if x.type == 2 and len(x.commonVariables) == 0)
        
        if no_cvars_max_length == length:
            length -= 1
            
    args = ', '.join(['t{}'.format(str(x+1)) for x in xrange(length)])
    c_args = ', '.join(['c{}'.format(str(x+1)) for x in xrange(length)])

    # If in the end the length is 0 that means that the intList will be empty. In that
    # case doesn't make too much sense to emit code for it as it would only trigger a
    # warning from the c compiler
    if length > 0:
        if GenerationData.compositionStructures['Successors'] == 'Queue':
            outfile.write('{}unsigned int {};\n'.format(spaces_level_1,
                                                        c_args))
            outfile.write('{}uIntArrayQueuePtr {};\n'.format(spaces_level_1,
                                                             args))
        elif GenerationData.compositionStructures['Successors'] == 'Stack':
            outfile.write('{}uIntListStackNodePtr {};\n'.format(spaces_level_1,
                                                                args))

def fillDataStructureLevelNodes(outfile):
    # Auxiliar clousure function name to get the name of the structure to be used to represent the set leaf
    def get_set_leaf_structure_name():
        if GenerationData.compositionStructures['Sets'] == 'Judy': return 'Pvoid_t'
        elif GenerationData.compositionStructures['Sets'] == 'BitMap': return 'BitMap'
        elif GenerationData.compositionStructures['Sets'] == 'AVLTree': return 'AVLTree'
        elif GenerationData.compositionStructures['Sets'] == 'BTree': return 'BTreeSet'
        else: return 'UNKNOWN'
    # Auxiliar clousure function name to get the name of the structure to be used to represent the successors list
    def get_successors_structure_name():
        if GenerationData.compositionStructures['Successors'] == 'Stack': return 'uIntListStack'
        elif GenerationData.compositionStructures['Successors'] == 'Queue': return 'uIntArrayQueue'
        else: return 'UNKNOWN'

    #equationsTable = GenerationData.equationsTable
    #viewNamesToCombinations = GenerationData.viewsData.viewNamesToCombinations
    answersToStore = GenerationData.answersToStore
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    
    spaces_level_1 = SPACES

    # Store the answers by length. This will be used to know in which level node store the
    # answers
    lengthToPreds = defaultdict(set)
    for rule in getEquationsFromAllStratums():
        if len(rule.rightArguments) > 1:
            lengthToPreds[len(rule.rightArguments)].add(rule.rightVariable.id)
            
    
    viewsData = []
    #print viewNamesToCombinations
    viewLengths = list((len(x) for x in viewNamesToCombinations.itervalues()))
    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    
    lengths = list(xrange(2, number_of_data_structure_nodes+1))
    for length in lengths:
        viewsData.append((length, viewLengths.count(length)))

    for pos, length in enumerate(lengths):
        number_of_views_for_this_level = sum((x[1]) for x in viewsData 
                                             if x[0] >= length)

        outfile.write('/* Level {} */\n'.format(length))
        outfile.write('struct DsData_Level_{}'.format(length))
        outfile.write('{\n')

        # If the number of views for this level is 0 we don't have to emit code
        # to store the intList for the current level, also it would output m[0]
        # forbidden by ISO C and with no sense.
        if number_of_views_for_this_level:
            outfile.write('{}{} m[{}];\n'.format(spaces_level_1,
                                                 get_successors_structure_name(),
                                                 number_of_views_for_this_level))
        
        # Emit code to store the answers required by the level node
        for variable_id in lengthToPreds[length]:
            if variable_id in answersToStore:
                outfile.write('{}{} R{};\n'.format(spaces_level_1,
                                                   get_set_leaf_structure_name(),
                                                   variable_id.name))
                
        # Check if we have to add a new solution because there is a predicate having
        # all the variables the same Equal card or there is a predicate having all
        # its variables part of the set of common variables  
        #for pred in chain(getPredicatesWithAllVariablesBeingTheSameEqualCard(),
        #                  getPredicatesWithAllVariablesBeingInTheSharedSet(),
        #                  getPredicatesWithAllVariablesBeingInTheSharedSetIncludingConstants()):
        for variable_id in getAllSolutions():
            if variable_id not in answersToStore and getPredicateLength(variable_id) == length:
                outfile.write('{}{} R{};\n'.format(spaces_level_1,
                                                   get_set_leaf_structure_name(),
                                                   variable_id.name))
               
        if pos != len(lengths) - 1:
            # This is purely esthetic if we have some views in the level we 
            # print a blank line to split the intList declaration from the
            # level declaration clearly
            if number_of_views_for_this_level:
                outfile.write('\n')
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{}Pvoid_t level{};\n'.format(spaces_level_1,
                                                            length+1))
            elif GenerationData.compositionStructures['Paths'] == 'Hash':
                outfile.write('{}HashTable level{};\n'.format(spaces_level_1,
                                                              length+1))
            elif GenerationData.compositionStructures['Paths'] == 'BTree':
                outfile.write('{}BTree level{};\n'.format(spaces_level_1,
                                                          length+1))
            
            
            
        outfile.write('};\n')
        outfile.write('typedef struct DsData_Level_{0} DsData_{0};\n\n'.format(length))
        
        outfile.write('DsData_{0} * DsData_Level_{0}_new_node();\n'.format(length))
        outfile.write('void DsData_Level_{0}_init(DsData_{0} *);\n'.format(length))
        if GenerationData.compositionStructures['Paths'] == 'BTree':
            outfile.write('void DsData_Level_{0}_free(size_t);\n'.format(length))
        else:
            outfile.write('void DsData_Level_{0}_free(DsData_{0} *);\n'.format(length))
        outfile.write('\n')
        
    #outfile.write('\n')

@check_for_predicates_of_type2    
def fillDataStructureInsertFunctions(outfile):
    def print_code_for_Ds_insert_1():
        spaces_level_1 = SPACES
        spaces_level_2 = SPACES * 2
        spaces_level_3 = SPACES * 3
        
        outfile.write('void Ds_insert_1(int x_1){\n')
        
        if GenerationData.compositionStructures['Paths'] == 'Judy':
            outfile.write('{}Word_t * PValue1;\n\n'.format(spaces_level_1))
            outfile.write('{}if (!(JLG(PValue1, root, x_1))){{\n'.format(spaces_level_1))
    
            outfile.write('{}JLI(PValue1, root, x_1);\n'.format(spaces_level_2))
            outfile.write('{}if (PValue1 == PJERR){{\n'.format(spaces_level_2))
    
            outfile.write('{}fprintf(stderr, "Solver: Error allocating '.format(spaces_level_3))
            outfile.write('memory %s:%i\\n", __FILE__, __LINE__);\n')
            outfile.write('{}abort();\n'.format(spaces_level_3))
    
            outfile.write('{}}}\n'.format(spaces_level_2))
            
            if getDataStructureNodesMaximumLength() > 1:
                outfile.write('{}(*PValue1) = ((Word_t) DsData_Level_2_new_node());\n'.format(spaces_level_2))
            else:
                outfile.write('{}(*PValue1) = (Word_t) NULL;\n'.format(spaces_level_2))
    
            outfile.write('{}}}\n'.format(spaces_level_1))
        
        elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
          GenerationData.compositionStructures['Paths'] == 'BTree':
            function_name = 'HashTable'
            ampersand = '&'
            if GenerationData.compositionStructures['Paths'] == 'BTree':
                function_name = 'BTree'
                ampersand = ''

            outfile.write('{}Cell * c_1;\n\n'.format(spaces_level_1))
            outfile.write('{}if (!(c_1 = {}_Lookup({}root, x_1))){{\n'.format(spaces_level_1, 
                                                                              function_name,
                                                                              ampersand))
            outfile.write('{}c_1 = {}_Insert(&root, x_1);\n'.format(spaces_level_2, function_name))
            
            if getDataStructureNodesMaximumLength() > 1:
                outfile.write('{}c_1->value = (size_t) DsData_Level_2_new_node();\n'.format(spaces_level_2))
            else:
                outfile.write('{}c_1->value = (size_t) NULL;\n'.format(spaces_level_2))
            
            outfile.write('{}}}\n'.format(spaces_level_1))
        else:
            raise KeyError('Unknown data structure to represent the paths')
        
        outfile.write('}\n')
            
        
    # Auxiliar clousure function name to get the name of the structure to be used to represent the successors list
    def get_successors_structure_name():
        if GenerationData.compositionStructures['Successors'] == 'Stack': return 'uIntListStack_append'
        elif GenerationData.compositionStructures['Successors'] == 'Queue': return 'uIntArrayQueue_append'
        else: return 'UNKNOWN'

    # Here we emit code to deal with the views. The length of the views is the same of the
    # length of the predicate it represents. Views can only exist for predicates on the 
    # right side of the rules so we take the minimum and maximum lengths of the predicates
    # of right side of the rules and emit functions for those values and the values in between
    # As we don't store a level 1 node if the minimum length we have is 1, we need to
    # emit slightly different code that is why the auxiliary function print_code_for_Ds_insert_1()
    # is created and called if we detect a minimum length of 1
    lengths = xrange(getQueryMinimumLength(), getQueryMaximumLength()+1)
    
    spaces_level_1 = SPACES
    spaces_level_2 = SPACES * 2
    spaces_level_3 = SPACES * 3

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

        if GenerationData.compositionStructures['Paths'] == 'Judy':
            values = ('* PValue{}'.format(str(v+1)) for v in xrange(length-1))
            outfile.write('{}Word_t {};\n\n'.format(spaces_level_1,
                                                    ', '.join(values)))
        elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
          GenerationData.compositionStructures['Paths'] == 'BTree':
            values = ('* c_{}'.format(str(v+1)) for v in xrange(length-1))
            outfile.write('{}Cell {};\n\n'.format(spaces_level_1,
                                                  ', '.join(values)))
        
        for x in xrange(1, length):
            if x == 1:
                node = 'root'
            else:
                if GenerationData.compositionStructures['Paths'] == 'Judy':
                    node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)
                elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
                  GenerationData.compositionStructures['Paths'] == 'BTree':
                    node = '((DsData_{} *) c_{}->value)->level{}'.format(x, x-1, x+1)
            
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{0}if (!(JLG(PValue{1}, {2}, x_{1})))'.format(spaces_level_1, x,
                                                                             node))
            elif GenerationData.compositionStructures['Paths'] == 'Hash':
                outfile.write('{0}if (!(c_{1} = HashTable_Lookup(&{2}, x_{1})))'.format(spaces_level_1, x,
                                                                                        node))
            elif GenerationData.compositionStructures['Paths'] == 'BTree':
                outfile.write('{0}if (!(c_{1} = BTree_Lookup({2}, x_{1})))'.format(spaces_level_1, x,
                                                                                   node))
                
            outfile.write('{\n')

            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{0}JLI(PValue{1}, {2}, x_{1});\n'.format(spaces_level_2, x,
                                                                        node))
                outfile.write('{0}if (PValue{1} == PJERR)'.format(spaces_level_2, x))
                outfile.write('{\n')
    
                outfile.write('{}fprintf(stderr, "Solver: Error '.format(spaces_level_3))
                outfile.write('allocating memory %s:%i\\n", __FILE__, __LINE__);\n')
                
                outfile.write('{}abort();\n'.format(spaces_level_3))
    
                outfile.write('{}'.format(spaces_level_2))
                outfile.write('}\n')
                outfile.write('{}(*PValue{}) = ((Word_t) DsData_Level_{}_new_node());\n'.format(spaces_level_2,
                                                                                                 x, x+1))
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                structure_name = 'HashTable'
                if GenerationData.compositionStructures['Paths'] == 'BTree':
                    structure_name = 'BTree'

                outfile.write('{0}c_{1} = {2}_Insert(&{3}, x_{1});\n'.format(spaces_level_2, x,
                                                                             structure_name, node))
                outfile.write('{0}c_{1}->value = (size_t) DsData_Level_{2}_new_node();\n'.format(spaces_level_2,
                                                                                                 x, x+1))
                

            outfile.write('{}'.format(spaces_level_1))
            outfile.write('}\n\n')
            
        for x in xrange(2, length+1):
            returning_node = ''
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                returning_node = '*PValue{}'.format(x-1)
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                returning_node = 'c_{}->value'.format(x-1)
                
            outfile.write('{}{}(&((DsData_{} *)'.format(spaces_level_1, 
                                                        get_successors_structure_name(),
                                                        x))
            outfile.write(' {})->m[pos], x_{});\n'.format(returning_node, x))
            
        outfile.write('}\n\n')

@check_for_predicates_of_type2        
def fillDataStructureGetIntListFunctions(outfile):
    # Auxiliar clousure function name to get the name of the structure to be used to represent the successors list
    def get_successors_structure_name():
        if GenerationData.compositionStructures['Successors'] == 'Stack': return 'uIntListStackNodePtr'
        elif GenerationData.compositionStructures['Successors'] == 'Queue': return 'uIntArrayQueuePtr'
        else: return 'UNKNOWN'
    #equationsTable = GenerationData.equationsTable
    
    # Here we emit source code for the functions to retrieve the lists we need
    # to iterate to obtain new solutions basically we have to add a new 
    # function for every variable previously emitted in the fillIntList 
    # function in this module. As we have to emit code for those variables the
    # way in which the value is computed is the same. May be this functionality
    # could be refactored into a new function. For more detailed explanation on
    # how to compute those values please check the fillIntList function
    
    requires_t0 = any(len(x.commonVariables) == 0 for x in getEquationsFromAllStratums() if x.type == 2)
    length = getQueryMaximumLength() - 1
    
    if requires_t0:
        no_cvars_max_length = max(len(x.consultingArguments) for x in getEquationsFromAllStratums()
                                  if x.type == 2 and len(x.commonVariables) == 0)
        if no_cvars_max_length == length:
            length -= 1
            
    # This loop is in charge to emit the source code of the different functions 
    # required to retrieve the different lists. We add one to the length as the
    # xrange functions goes to length - 1. We start in 1 as the 0 value is
    # reserved in the template to retrieve the values of the root.
    for length in xrange(1, length+1):
        args_to_function = ('int x_{}'.format(str(v+1)) for v in xrange(length))
        outfile.write('{} Ds_get_intList_{}(int pos, {})'.format(get_successors_structure_name(),
                                                                 length,
                                                                 ", ".join(args_to_function)))
        outfile.write('{\n')
        spaces = SPACES
        
        if GenerationData.compositionStructures['Paths'] == 'Judy':
            values = ('* PValue{}'.format(str(v+1)) for v in xrange(length))
            outfile.write('{}Word_t {};\n\n'.format(spaces,
                                                    ', '.join(values)))
        elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
          GenerationData.compositionStructures['Paths'] == 'BTree':
            values = ('* c_{}'.format(str(v+1)) for v in xrange(length))
            outfile.write('{}Cell {};\n\n'.format(spaces,
                                                  ', '.join(values)))
        
        for x in xrange(1, length+1):
            if x == 1:
                node = 'root'
            else:
                if GenerationData.compositionStructures['Paths'] == 'Judy':
                    node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)
                elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
                  GenerationData.compositionStructures['Paths'] == 'BTree':
                    node = '((DsData_{} *) c_{}->value)->level{}'.format(x, x-1, x+1)
            
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{}if ((JLG(PValue{}, {}, x_{})))'.format(spaces, str(x),
                                                                        node, str(x)))
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                structure_name = 'HashTable'
                ampersand = '&'
                if GenerationData.compositionStructures['Paths'] == 'BTree':
                    structure_name = 'BTree'
                    ampersand = ''
                    
                outfile.write('{0}if ((c_{1} = {2}_Lookup({3}{4}, x_{1})))'.format(spaces, str(x), 
                                                                                   structure_name, 
                                                                                   ampersand,
                                                                                   node))

            outfile.write('{\n')
            spaces += SPACES
            
        returning_node = ''
        if GenerationData.compositionStructures['Paths'] == 'Judy':
            returning_node = '*PValue{}'.format(length)
        elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
          GenerationData.compositionStructures['Paths'] == 'BTree':
            returning_node = 'c_{}->value'.format(length)
            
        if GenerationData.compositionStructures['Successors'] == 'Stack':
            outfile.write('{}return ((DsData_{} *) {})->m[pos].head;\n'.format(spaces,
                                                                               str(length+1),
                                                                               returning_node))
        elif GenerationData.compositionStructures['Successors'] == 'Queue':
            outfile.write('{}return &((DsData_{} *) {})->m[pos];\n'.format(spaces,
                                                                           str(length+1),
                                                                           returning_node))
        else:
            error = "Don't know how to generate code for the data structure"
            error += " {} ".format(GenerationData.compositionStructures['Successors'])
            error += "at function fillDataStructureGetIntListFunctions"
            raise KeyError(error)
            
        for x in xrange(1, length+1):
            spaces = spaces[:-len(SPACES)]
            outfile.write('{}'.format(spaces))
            outfile.write('}\n')
        
        if GenerationData.compositionStructures['Successors'] == 'Queue':
            outfile.write('\n{}return &queue_not_found;\n'.format(spaces))
        else:
            outfile.write('\n{}return NULL;\n'.format(spaces))
        
        outfile.write('}\n\n')
        
def fillDataStructureContainSolutionFunctions(outfile):
    for variable_id in getAllSolutions():
        # Get the length of the predicate
        length = getPredicateLength(variable_id)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('int Ds_contains_solution_{}({})'.format(variable_id.name,
                                                               ', '.join(args)))
        outfile.write('{\n')
        spaces = SPACES
        if length > 1:
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                values = ('* PValue{}'.format(str(v+1)) for v in xrange(length-1))
                outfile.write('{}Word_t {};\n\n'.format(spaces,
                                                        ', '.join(values)))
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                values = ('* c_{}'.format(str(v+1)) for v in xrange(length-1))
                outfile.write('{}Cell {};\n\n'.format(spaces,
                                                      ', '.join(values)))
        
        for x in xrange(1, length):
            if x == 1:
                node = 'root'
            else:
                if GenerationData.compositionStructures['Paths'] == 'Judy':
                    node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)
                elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
                  GenerationData.compositionStructures['Paths'] == 'BTree':
                    node = '((DsData_{} *) c_{}->value)->level{}'.format(x, x-1, x+1)
                    
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{0}if (!(JLG(PValue{1}, {2}, x_{1})))\n'.format(spaces,
                                                                               x, node))
            elif GenerationData.compositionStructures['Paths'] == 'Hash':
                outfile.write('{0}if (!(c_{1} = HashTable_Lookup(&{2}, x_{1})))\n'.format(spaces,
                                                                                          x, node))
            elif GenerationData.compositionStructures['Paths'] == 'BTree':
                outfile.write('{0}if (!(c_{1} = BTree_Lookup({2}, x_{1})))\n'.format(spaces,
                                                                                      x, node))
                
            spaces += SPACES
            outfile.write('{}return false;\n'.format(spaces))
            spaces = spaces[:-len(SPACES)]
            
        if length > 1:
            outfile.write('\n')
            returning_node = ''
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                returning_node = '*PValue{}'.format(length-1)
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                returning_node = 'c_{}->value'.format(length-1)
                
            node = '((DsData_{} *) {})->R{}'.format(str(length),
                                                    returning_node,
                                                    variable_id.name)
        else:
            node = 'R{}'.format(variable_id.name)
        
        if GenerationData.compositionStructures['Sets'] == 'BitMap':
            outfile.write('{}return BitMap_testBit(&{}, x_{});\n'.format(spaces,
                                                                         node,
                                                                         length))
        elif GenerationData.compositionStructures['Sets'] == 'Judy':
            outfile.write('{}return Judy1Test({}, x_{}, PJE0);\n'.format(spaces,
                                                                         node,
                                                                         length))
        elif GenerationData.compositionStructures['Sets'] == 'AVLTree':
            outfile.write('{}return AVLTree_contains({}, x_{});\n'.format(spaces,
                                                                          node,
                                                                          length))
        elif GenerationData.compositionStructures['Sets'] == 'BTree':
            outfile.write('{}return BTreeSet_Contains({}, x_{});\n'.format(spaces,
                                                                           node,
                                                                           length))
        else:
            error = "Don't know how to generate code for the data structure"
            error += " {} ".format(GenerationData.compositionStructures['Successors'])
            error += "at function fillDataStructureContainSolutionFunctions"
            raise KeyError(error)
            
        outfile.write('}\n\n')
        
def fillDataStructureAppendSolutionFunctions(outfile):
    for variable_id in getAllSolutions():
        # Get the length of the predicate
        length = getPredicateLength(variable_id)
        args = ('int x_{}'.format(str(x)) for x in xrange(1, length+1))
        outfile.write('void Ds_append_solution_{}({})'.format(variable_id.name,
                                                               ', '.join(args)))
        outfile.write('{\n')
        spaces = SPACES
        if length > 1:
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                values = ('* PValue{}'.format(str(v+1)) for v in xrange(length-1))
                outfile.write('{}Word_t {};\n\n'.format(spaces,
                                                        ', '.join(values)))
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                values = ('* c_{}'.format(str(v+1)) for v in xrange(length-1))
                outfile.write('{}Cell {};\n\n'.format(spaces,
                                                      ', '.join(values)))
        for x in xrange(1, length):
            if x == 1:
                node = 'root'
            else:
                if GenerationData.compositionStructures['Paths'] == 'Judy':
                    node = '((DsData_{} *) *PValue{})->level{}'.format(x, x-1, x+1)
                elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
                  GenerationData.compositionStructures['Paths'] == 'BTree':
                    node = '((DsData_{} *) c_{}->value)->level{}'.format(x, x-1, x+1)
            
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{0}if (!(JLG(PValue{1}, {2}, x_{1})))'.format(spaces,
                                                                             x,
                                                                             node))
                outfile.write('{\n')
                spaces += SPACES
                outfile.write('{0}JLI(PValue{1}, {2}, x_{1});\n'.format(spaces,
                                                                        x,
                                                                        node))
                outfile.write('{0}if (PValue{1} == PJERR)'.format(spaces,
                                                                  x))
                outfile.write('{\n')
                spaces += SPACES
                outfile.write('{}fprintf(stderr, "Solver: Error '.format(spaces))
                outfile.write('allocating memory %s:%i\\n", __FILE__, __LINE__);\n')
                
                outfile.write('{}abort();\n'.format(spaces))
                spaces = spaces[:-len(SPACES)]
                outfile.write('{}'.format(spaces))
                outfile.write('}\n')
                outfile.write('{}(*PValue{}) = ((Word_t) DsData_Level_{}_new_node());\n'.format(spaces,
                                                                                                x, x+1))
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                structure_name = 'HashTable'
                ampersand = '&'
                if GenerationData.compositionStructures['Paths'] == 'BTree':
                    structure_name = 'BTree'
                    ampersand = ''
                     
                outfile.write('{0}if (!(c_{1} = {2}_Lookup({3}{4}, x_{1})))'.format(spaces, x,
                                                                                    structure_name, 
                                                                                    ampersand, 
                                                                                    node))
                outfile.write('{\n')
                spaces += SPACES
                outfile.write('{0}c_{1} = {2}_Insert(&{3}, x_{1});\n'.format(spaces, x, 
                                                                             structure_name, node))
                outfile.write('{}c_{}->value = (size_t) DsData_Level_{}_new_node();\n'.format(spaces,
                                                                                              x, x+1))
                
            
            spaces = spaces[:-len(SPACES)]
            outfile.write('{}'.format(spaces))
            outfile.write('}\n\n')
        
        if length > 1:
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                node = '((DsData_{} *) *PValue{})->R{}'.format(str(length),
                                                               str(length-1),
                                                               variable_id.name)
            elif GenerationData.compositionStructures['Paths'] == 'Hash' or\
              GenerationData.compositionStructures['Paths'] == 'BTree':
                node = '((DsData_{} *) c_{}->value)->R{}'.format(str(length),
                                                                 str(length-1),
                                                                 variable_id.name)
        else:
            node = 'R{}'.format(variable_id.name)
        
        if GenerationData.compositionStructures['Sets'] == 'Judy':
            outfile.write('{}if (Judy1Set(&{}, x_{}, PJE0) == JERR)'.format(spaces,
                                                                            node,
                                                                            str(length)))
            outfile.write('{\n')
            spaces += SPACES
            outfile.write('{}fprintf(stderr, "Solver: Error '.format(spaces))
            outfile.write('allocating memory %s:%i\\n", __FILE__, __LINE__);\n')
            outfile.write('{}abort();\n'.format(spaces))
            spaces = spaces[:-len(SPACES)]
            outfile.write('{}'.format(spaces))
            outfile.write('}\n')
        elif GenerationData.compositionStructures['Sets'] == 'BitMap':
            outfile.write('{}BitMap_setBit(&{}, x_{});\n'.format(spaces,
                                                                 node,
                                                                 str(length)))
        elif GenerationData.compositionStructures['Sets'] == 'AVLTree':
            outfile.write('{0}{1} = AVLTree_insert({1}, x_{2});\n'.format(spaces,
                                                                          node,
                                                                          str(length)))
        elif GenerationData.compositionStructures['Sets'] == 'BTree':
            outfile.write('{0}BTreeSet_Insert({1}, x_{2});\n'.format(spaces,
                                                                     node,
                                                                     str(length)))
        else:
            error = "Don't know how to generate code for the data structure"
            error += " {} ".format(GenerationData.compositionStructures['Successors'])
            error += "at function fillDataStructureAppendSolutionFunctions"
            raise KeyError(error)
        
        outfile.write('}\n\n')

def fillDataStructureInitLevelFunctions(outfile):
    def emit_code_set_leaf_init_function(spaces, name):
        if GenerationData.compositionStructures['Sets'] == 'Judy':
            outfile.write('{}d->R{} = (Pvoid_t) NULL;\n'.format(spaces,
                                                                name))
        elif GenerationData.compositionStructures['Sets'] == 'BitMap':
            outfile.write('{}BitMap_init(&d->R{});\n'.format(spaces,
                                                             name))
        elif GenerationData.compositionStructures['Sets'] == 'AVLTree':
            outfile.write('{}AVLTree_init(&d->R{});\n'.format(spaces,
                                                              name))
        elif GenerationData.compositionStructures['Sets'] == 'BTree':
            outfile.write('{}d->R{} = BTreeSet_Init();\n'.format(spaces,
                                                                 name))
        else:
            error = "Don't know how to generate code for the data structure"
            error += " {} ".format(GenerationData.compositionStructures['Sets'])
            error += "at function fillDataStructureInitLevelFunctions"
            raise KeyError(error)
        
    #equationsTable = GenerationData.equationsTable
    answersToStore = GenerationData.answersToStore
    #viewNamesToCombinations = GenerationData.viewsData.viewNamesToCombinations
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))
    
    lengthToPreds = defaultdict(set)
    for rule in getEquationsFromAllStratums():
        if len(rule.rightArguments) > 1:
            lengthToPreds[len(rule.rightArguments)].add(rule.rightVariable.id)
        
    viewLengths = list((len(x) for x in viewNamesToCombinations.itervalues()))
    viewsData = []
    
    # As we don't store a level0 type of node the minimum length we can have here is 2, that 
    # is the reason why the max value between the minimum query value and 2 is used.
    #lengths = xrange(max(getQueryMinimumLength(), 2), getQueryMaximumLength()+1)
    lengths = xrange(2, getDataStructureNodesMaximumLength() + 1)
    for length in lengths:
        viewsData.append((length, viewLengths.count(length)))

    for pos, length in enumerate(lengths):
        number_of_views_for_this_level = sum((x[1]) for x in viewsData
                                             if x[0] >= length)
        
        outfile.write('void DsData_Level_{0}_init(DsData_{0} *d)'.format(length))
        outfile.write('{\n')
        spaces_level_1 = SPACES
        
        if GenerationData.compositionStructures['Successors'] == 'Stack':
            outfile.write('{}'.format(spaces_level_1))
            
        for i in xrange(number_of_views_for_this_level):
            if GenerationData.compositionStructures['Successors'] == 'Queue':
                outfile.write('{}uIntArrayQueue_init(&d->m[{}]);\n'.format(spaces_level_1, i))
            elif GenerationData.compositionStructures['Successors'] == 'Stack':
                outfile.write('d->m[{}].head = '.format(i))
    
                if ((i%4) == 0 and i > 0):
                    outfile.write('NULL;\n');
                    if i != (number_of_views_for_this_level-1):
                        outfile.write('{}'.format(spaces_level_1));
            else:
                error = "Don't know how to generate code for the data structure"
                error += " {} ".format(GenerationData.compositionStructures['Successors'])
                error += "at function fillDataStructureInitLevelFunctions"
                raise KeyError(error)

        if GenerationData.compositionStructures['Successors'] == 'Stack':
            if (((number_of_views_for_this_level-1) % 4) != 0 or
                (number_of_views_for_this_level == 1)):
                    outfile.write('NULL;\n');

        outfile.write('\n')
        if pos != len(lengths)-1:
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{}d->level{} = (Pvoid_t) NULL;\n'.format(spaces_level_1,
                                                                        length + 1))
            elif GenerationData.compositionStructures['Paths'] == 'Hash':
                outfile.write('{}HashTable_Init(&d->level{});\n'.format(spaces_level_1,
                                                                        length + 1))
            elif GenerationData.compositionStructures['Paths'] == 'BTree':
                outfile.write('{}d->level{} = BTree_Init();\n'.format(spaces_level_1,
                                                                      length + 1))
            
        for variable_id in lengthToPreds[length]:
            if variable_id in answersToStore:
                emit_code_set_leaf_init_function(spaces_level_1, variable_id.name)
                
        # This has been extracted from the function fillDataStructureLevelNodes
        # to cover some edge cases regarding the status of a variable as a solution
        for variable_id in getAllSolutions():
            if variable_id not in answersToStore and getPredicateLength(variable_id) == length:
                emit_code_set_leaf_init_function(spaces_level_1, variable_id.name)
                    
        outfile.write('}\n')
   
def fillDataStructureLevelNewNodeFunctions(outfile):
    number_of_data_structure_nodes = getDataStructureNodesMaximumLength()
    # This checks that we don't handle level 1 nodes as for the current generation model doesn't 
    # contemplate the possibility of having a level 1 node. 
    #if min_value == 1: min_value += 1
    #lengths = xrange(min_value, number_of_data_structure_nodes + 1)
    lengths = xrange(2, number_of_data_structure_nodes + 1)

    spaces_level_1 = SPACES

    for length in lengths:
        node = 'DsData_{}'.format(length)
        outfile.write('{} * DsData_Level_{}_new_node()'.format(node,
                                                               length))
        outfile.write('{\n')
        outfile.write('{}{} * temp;\n\n'.format(spaces_level_1,
                                                node))
        outfile.write('{}temp = malloc(sizeof({}));\n'.format(spaces_level_1,
                                                              node))
        #outfile.write('{}memset(temp, 0, sizeof({}));\n\n'.format(spaces_level_1,
        #                                                          node))
        outfile.write('{}DsData_Level_{}_init(temp);\n\n'.format(spaces_level_1,
                                                                 length))
        outfile.write('{}return temp;\n'.format(spaces_level_1))
        outfile.write('}\n\n')

def fillDataStructureLevelFreeFunctions(outfile):
    #equationsTable = GenerationData.equationsTable
    answersToStore = GenerationData.answersToStore
    
    viewNamesToCombinations = dict(chain(*[ view.viewNamesToCombinations.items() for view in getViewsFromAllStratums() ]))

    lengthToPreds = defaultdict(set)
    for rule in getEquationsFromAllStratums():
        if len(rule.rightArguments) > 1:
            lengthToPreds[len(rule.rightArguments)].add(rule.rightVariable.id)
        
    viewLengths = list((len(x) for x in viewNamesToCombinations.itervalues()))
    viewsData = []

    # This checks that we don't handle level 1 nodes as for the current generation model doesn't 
    # contemplate the possibility of having a level 1 node.
    #if min_value == 1: min_value += 1
    #lengths = xrange(min_value, max_value + 1)
    lengths = xrange(2, getDataStructureNodesMaximumLength() + 1)
    
    for length in lengths:
        viewsData.append((length, viewLengths.count(length)))
    
    lengthToPreds = defaultdict(set)
    for rule in getEquationsFromAllStratums():
        lengthToPreds[len(rule.rightArguments)].add(rule.rightVariable.id)
        
    for pos, length in enumerate(lengths):
        spaces = SPACES
        
        if GenerationData.compositionStructures['Paths'] == 'BTree':
            outfile.write('void DsData_Level_{0}_free(size_t node){{\n'.format(length))
            outfile.write('{0}DsData_{1} *d = (DsData_{1} *) node;\n'.format(spaces, length))
        else:
            outfile.write('void DsData_Level_{0}_free(DsData_{0} *d)'.format(length))
            outfile.write('{\n')
        if pos != len(lengths) - 1:
            if GenerationData.compositionStructures['Paths'] == 'Judy':
                outfile.write('{}Word_t * PValue, index = 0;\n\n'.format(spaces))
                outfile.write('{}JLF(PValue, d->level{}, index);\n'.format(spaces,
                                                                           length+1))
                outfile.write('{}while (PValue != NULL)'.format(spaces))
                outfile.write('{\n')
                spaces += SPACES
                outfile.write('{0}DsData_Level_{1}_free((DsData_{1} *) *PValue);\n'.format(spaces,
                                                                                           length+1))
                outfile.write('{}JudyLDel(&d->level{}, index, PJE0);\n'.format(spaces,
                                                                               length+1))
                outfile.write('{}JLN(PValue, d->level{}, index);\n'.format(spaces,
                                                                           length+1))
                spaces = spaces[:-len(SPACES)]
                outfile.write('{}'.format(spaces))
                outfile.write('}\n')
            elif GenerationData.compositionStructures['Paths'] == 'Hash':
                node = 'd->level{0}.m_cells[i].value'.format(length+1)
                outfile.write('{}size_t i;\n\n'.format(spaces))
                outfile.write('{}for (i=0; i < d->level{}.m_arraySize; i++)\n'.format(spaces, length+1))
                spaces += SPACES
                outfile.write('{}if ({})\n'.format(spaces, node))
                spaces += SPACES
                outfile.write('{0}DsData_Level_{1}_free((DsData_{1} *) {2});\n\n'.format(spaces, length+1, node))
                spaces = spaces[:-len(SPACES)]
                spaces = spaces[:-len(SPACES)]
            elif GenerationData.compositionStructures['Paths'] == 'BTree':
                outfile.write('{0}BTree_Free(d->level{1}, DsData_Level_{1}_free);\n'.format(spaces, length+1))
            else:
                raise KeyError('Unknown paths data structure')
            
        number_of_views_for_this_level = sum((x[1]) for x in viewsData
                                             if x[0] >= length)
        for i in xrange(number_of_views_for_this_level):
            if GenerationData.compositionStructures['Successors'] == 'Queue':
                outfile.write('{}uIntArrayQueue_free(&d->m[{}]);\n'.format(spaces, i))
            elif GenerationData.compositionStructures['Successors'] == 'Stack':
                outfile.write('{}uIntListStack_free(&d->m[{}]);\n'.format(spaces, i))
        outfile.write('\n');
        
        
        for variable_id in lengthToPreds[length]:
            if variable_id in answersToStore:
                if GenerationData.compositionStructures['Sets'] == 'BitMap':
                    outfile.write('{}BitMap_free(&d->R{});\n'.format(spaces,
                                                                     variable_id.name))
                elif GenerationData.compositionStructures['Sets'] == 'AVLTree':
                    outfile.write('{}AVLTree_free(d->R{});\n'.format(spaces,
                                                                      variable_id.name))
                elif GenerationData.compositionStructures['Sets'] == 'Judy':
                    outfile.write('{}Judy1FreeArray(&d->R{}, PJE0);\n'.format(spaces,
                                                                              variable_id.name))
                elif GenerationData.compositionStructures['Sets'] == 'BTree':
                    outfile.write('{}BTreeSet_Free(d->R{});\n'.format(spaces,
                                                                   variable_id.name))
                else:
                    error = "Don't know how to generate code for the data structure"
                    error += " {} ".format(GenerationData.compositionStructures['Sets'])
                    error += "at function fillDataStructureLevelFreeFunctions"
                    raise KeyError(error)
                
        outfile.write('{}*&d = NULL;\n'.format(spaces))
        outfile.write('}\n\n')

# The level 1 node is currently treated differently from the other type of nodes
# of the data-structure (this is a implentation decision).  
# We check for all the possible solutions of length 1 or predicates and emit code
# appropriately.
def fillDataStructureRootSolutions(outfile):
    def get_set_leaf_structure_name():
        if GenerationData.compositionStructures['Sets'] == 'Judy': return 'Pvoid_t'
        elif GenerationData.compositionStructures['Sets'] == 'BitMap': return 'BitMap'
        elif GenerationData.compositionStructures['Sets'] == 'AVLTree': return 'AVLTree'
        elif GenerationData.compositionStructures['Sets'] == 'BTree': return 'BTreeSet'
        else: return 'UNKNOWN'
        
    (answers_of_length_1, predicates_in_rules_of_length_1) = getAnswersOfLength_1()
                
    if answers_of_length_1:
        outfile.write("/* Solution of length 1 */\n")
        line = ', '.join(['R{}'.format(variable_id.name) for variable_id in answers_of_length_1])
        outfile.write('static {} {};\n'.format(get_set_leaf_structure_name(), line))
        
    if predicates_in_rules_of_length_1:
        outfile.write("/* Predicates of length 1*/\n")
        line = ', '.join(['R{}'.format(variable_id.name) for variable_id in predicates_in_rules_of_length_1])
        outfile.write('static {} {};\n'.format(get_set_leaf_structure_name(), line))

# This function only should be executed if there are predicates of length 2
# If we only have type 1 rules we don't have level 2 nodes (as there is no database) 
# so this will cause an error. Another case we have to handle is that if even having
# rules of type 2 the maximum length is 1. 
@check_for_predicates_of_type2
def fillDataStructureLevel2Line(outfile):
    spaces_level_2 = SPACES * 2
    if getDataStructureNodesMaximumLength() > 1:
        outfile.write('{}DsData_Level_2_free((DsData_2 *) *PValue);\n'.format(spaces_level_2))
        
def fillStratumSolverQueues(outfile):
    number_of_stratums = len(GenerationData.stratums)
    queues = ", ".join('solver_queue' + str(x) for x in xrange(1, number_of_stratums+1))
    outfile.write('SolverQueue {};\n'.format(queues))
    
def fillDataStructureJudyHeader(outfile):
    if GenerationData.compositionStructures['Paths'] == 'Judy' or\
            GenerationData.compositionStructures['Sets'] == 'Judy':
        outfile.write('#include <Judy.h>\n')
        
def fill_DataStructureRootLevel(outfile):
    if GenerationData.compositionStructures['Paths'] == 'Judy':
        outfile.write('static Pvoid_t root;\n')
    elif GenerationData.compositionStructures['Paths'] == 'Hash':
        outfile.write('HashTable root;\n')
    elif GenerationData.compositionStructures['Paths'] == 'BTree':
        outfile.write('BTree root;\n')
    else:
        raise KeyError('Unknown data structure for paths')
        
def fillDataStructureScanZeroLevelVariables(outfile):
    if GenerationData.compositionStructures['Paths'] == 'Judy':
        outfile.write('Word_t zero_index;\n')
        outfile.write('short first_value;\n')
    elif GenerationData.compositionStructures['Paths'] == 'Hash':
        outfile.write('unsigned int zero_index;\n')
    elif GenerationData.compositionStructures['Paths'] == 'BTree':
        outfile.write('BTreeKeyList *zero_index;\n')
    else:
        raise KeyError('Unknown data structure for paths')
    
def fill_DataStructurefillLevelZeroInit(outfile):
    spaces = SPACES
    if GenerationData.compositionStructures['Paths'] == 'Judy':
        outfile.write('{}zero_index = 0;\n'.format(spaces))
        outfile.write('{}first_value = 1;\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'Hash':
        outfile.write('{}zero_index = 0;\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'BTree':
        outfile.write('{}zero_index = NULL;\n'.format(spaces))
        outfile.write('{}BTree_Fill_KeysList(root, &zero_index);\n'.format(spaces))
    else:
        raise KeyError('Unknown data structure for paths')
    
def fill_DataStructureGetZeroValues(outfile):
    spaces = SPACES
    if GenerationData.compositionStructures['Paths'] == 'Judy':
        outfile.write('{}Word_t * PValue;\n\n'.format(spaces))
        outfile.write('{}if (first_value){{\n'.format(spaces))
        outfile.write('{}first_value = 0;\n'.format(spaces * 2))
        outfile.write('{}JLF(PValue, root, zero_index);\n{}}}\n'.format(spaces * 2, spaces))
        outfile.write('{}else{{\n'.format(spaces))
        outfile.write('{}JLN(PValue, root, zero_index);\n{}}}\n\n'.format(spaces * 2, spaces))
        outfile.write('{}(*value) = zero_index;\n\n'.format(spaces))
        outfile.write('{}if (PValue){{\n'.format(spaces))
        outfile.write('{}return true;\n{}}}\n'.format(spaces * 2, spaces))
        outfile.write('{}return false;\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'Hash':
        outfile.write('{}while (zero_index < root.m_arraySize){{\n'.format(spaces))
        outfile.write('{}if (root.m_cells[zero_index].key){{\n'.format(spaces * 2))
        outfile.write('{}(*value) = root.m_cells[zero_index].key;\n'.format(spaces * 3))
        outfile.write('{}zero_index++;\n'.format(spaces * 3))
        outfile.write('{}return true;\n{}}}\n'.format(spaces * 3, spaces*2))
        outfile.write('{}zero_index++;\n{}}}\n'.format(spaces * 2, spaces))
        outfile.write('{}return false;\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'BTree':
        outfile.write('{}BTreeKeyList *temp;\n\n'.format(spaces))
        outfile.write('{}if (zero_index){{\n'.format(spaces))
        outfile.write('{}temp = zero_index;\n'.format(spaces*2))
        outfile.write('{}(*value) = zero_index->value;\n'.format(spaces*2))
        outfile.write('{}zero_index = zero_index->next;\n'.format(spaces*2))
        outfile.write('{}free(temp);\n'.format(spaces*2))
        outfile.write('{}return true;\n'.format(spaces*2))
        outfile.write('{}}}\n\n'.format(spaces))
        outfile.write('{}return false;\n'.format(spaces))
    else:
        raise KeyError('Unknown data structure for paths')
    
def fill_DataStructureInit(outfile):
    spaces = SPACES
    if GenerationData.compositionStructures['Paths'] == 'Judy':
        outfile.write('{}root = (Pvoid_t) NULL;\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'Hash':
        outfile.write('{}HashTable_Init(&root);\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'BTree':
        outfile.write('{}root = BTree_Init();\n'.format(spaces))
    else:
        raise KeyError('Unknown data structure for paths')
    
    if GenerationData.compositionStructures['Successors'] == 'Queue':
        outfile.write('{}memset(&queue_not_found, 0, sizeof(uIntArrayQueue));\n'.format(spaces))
    
    # The getAnswersOfLength_1 returns two sets. Using the reduce function
    # we convert them into one as it is more convenient for the iteration.
    for variable_id in reduce(lambda x,y: x.union(y), getAnswersOfLength_1()):
        if GenerationData.compositionStructures['Sets'] == 'Judy':
            outfile.write('{}R{} = NULL;\n'.format(spaces, variable_id.name))
        elif GenerationData.compositionStructures['Sets'] == 'BTree':
            outfile.write('{}R{} = BTreeSet_Init();\n'.format(spaces, variable_id.name))
        elif GenerationData.compositionStructures['Sets'] == 'AVLTree':
            outfile.write('{}AVLTree_init(&R{});\n'.format(spaces, variable_id.name))
        elif GenerationData.compositionStructures['Sets'] == 'BitMap':
            outfile.write('{}BitMap_init(&R{});\n'.format(spaces, variable_id.name))
        else:
            raise KeyError("Unknown data structure for Sets at DsInitLevel")
    
def fill_DataStructureFree(outfile):
    spaces = SPACES
    if GenerationData.compositionStructures['Paths'] == 'Judy':
        outfile.write('{}Word_t * PValue, index = 0;\n\n'.format(spaces))
        outfile.write('{}JLF(PValue, root, index);\n'.format(spaces))
        outfile.write('{}while (PValue != NULL){{;\n'.format(spaces))
        
        if getDataStructureNodesMaximumLength() > 1:
            outfile.write('{}DsData_Level_2_free((DsData_2 *) *PValue);\n\n'.format(spaces * 2))
        
        outfile.write('{}JudyLDel(&root, index, PJE0);\n'.format(spaces * 2))
        outfile.write('{}JLN(PValue, root, index);\n'.format(spaces * 2))
        outfile.write('{}}}\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'Hash':
        if getDataStructureNodesMaximumLength() > 1:
            outfile.write('{}unsigned int i;\n\n'.format(spaces))
            outfile.write('{}for (i = 0; i < root.m_arraySize; i++)\n'.format(spaces))
            outfile.write('{}if (root.m_cells[i].key)\n'.format(spaces*2))
            outfile.write('{}DsData_Level_2_free((DsData_2 *) root.m_cells[i].value);\n\n'.format(spaces*3))
            
        outfile.write('{}HashTable_Free(&root);\n'.format(spaces))
    elif GenerationData.compositionStructures['Paths'] == 'BTree':
        if getDataStructureNodesMaximumLength() > 1:
            outfile.write('{}BTree_Free(root, DsData_Level_2_free);\n'.format(spaces))
        
    
        
def fill_DataStructureQueueNotFound(outfile):
    if GenerationData.compositionStructures['Successors'] == 'Queue':
        outfile.write('/* Variable used to represent that a queue has not been found */\n')
        outfile.write('uIntArrayQueue queue_not_found;\n')
        
def fillMakefileLibs(outfile):
    if GenerationData.compositionStructures['Paths'] == 'Judy' or\
        GenerationData.compositionStructures['Sets'] == 'Judy':
        outfile.write('LIB   = -lm -lJudy\n')
    else:
        outfile.write('LIB   = -lm\n')
        

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
     'fill_StratumQueueInitializers' : fillStratumQueueInitializers,
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
     'fill_DsFreeLevel2Line'     : fillDataStructureLevel2Line,
     'fill_DsFillJudyHeader'     : fillDataStructureJudyHeader,
     'fill_DsRootLevel'          : fill_DataStructureRootLevel,
     'fill_DsScanZeroLevelVariables'  : fillDataStructureScanZeroLevelVariables,
     'fill_DsfillLevelZeroInit'  : fill_DataStructurefillLevelZeroInit,
     'fill_DsGetZeroValues'      : fill_DataStructureGetZeroValues,
     'fill_DsInit'               : fill_DataStructureInit,
     'fill_DsFree'               : fill_DataStructureFree,
     'fill_DsQueueNotFound'      : fill_DataStructureQueueNotFound,
     'fill_StratumSolverQueues'  : fillStratumSolverQueues,
     'fill_MakefileLibs'         : fillMakefileLibs
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
                                compositionStructures, predicateTypes, 
                                answersToStore, printVariables, 
                                idToStratumLevels):
    # Make the necessary data to generate the source code available to the rest of the functions
    GD = namedtuple('GD', ['stratums', 'predicateTypes', 'compositionStructures', 
                           'answersToStore', 'printVariables', 'idToStratumLevels'])
    
    globals()['GenerationData'] = GD(stratums, predicateTypes, compositionStructures,
                                     answersToStore, printVariables, idToStratumLevels)
    
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
