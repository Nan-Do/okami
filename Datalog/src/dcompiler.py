#!/usr/bin/env python
# encoding: utf-8
'''
dcompiler -- A Datalog compiler

dcompiler is a Datalog compiler it takes a datalog specification and generates a highly optimized c solver. 

@author:     Fernando Tarin Morales

@copyright:  2014 The University of Tokyo / National Institute of Informatics. All rights reserved.

@license:    license

@contact:    fernando@nii.ac.jp
@deffield    updated: Updated
'''

# Python Standar Library imports
import sys
import os
import pprint
import argparse
import logging

from itertools import chain
from collections import defaultdict
#from argparse import ArgumentParser
#from argparse import RawDescriptionHelpFormatter

# Compiler code imports
from BuildRulesTable import buildRulesTable
from RuleDecomposer import decomposeRulesFromFile, saveDecomposedRules
from RewritingEquationsGenerator import rewritingEquationGenerator, rewritingEquationPrinter
from PredicateOrder import predicateOrder
from RuleStratifier import stratifyRules
from Types import Stratum, Ordering

# Import the backends to generate the code
import c_Backend, py_Backend

__all__ = []
__version__ = 0.1
__date__ = '2014-02-18'
__updated__ = '2014-02-18'

DEBUG = 0
TESTRUN = 0
PROFILE = 0

class CLIError(Exception):
    '''Generic exception to raise and log different fatal errors.'''
    def __init__(self, msg):
        super(CLIError).__init__(type(self))
        self.msg = "E: %s" % msg
    def __str__(self):
        return self.msg
    def __unicode__(self):
        return self.msg

def main(argv=None): # IGNORE:C0111
    '''Command line options.'''

    if argv is None:
        argv = sys.argv
    else:
        sys.argv.extend(argv)

    program_name = os.path.basename(sys.argv[0])
    program_version = "v%s" % __version__
    program_build_date = str(__updated__)
    program_version_message = '%%(prog)s %s (%s)' % (program_version, program_build_date)
    program_shortdesc = __import__('__main__').__doc__.split("\n")[1]
    program_license = '''%s

  Created by Fernando Tarin Morales on %s.
  Copyright 2014 The University of Tokyo / National Institute of Informatics. All rights reserved.

  Licensed under the Apache License 2.0
  http://www.apache.org/licenses/LICENSE-2.0

  Distributed on an "AS IS" basis without warranties
  or conditions of any kind, either express or implied.

USAGE
''' % (program_shortdesc, str(__date__))

    try:
        # Setup argument parser
        parser = argparse.ArgumentParser(description='Compiler for datalog.')
        parser.add_argument('source_file', metavar='file.datalog', type=str, nargs=1,
                       help='The datalog program to compile')
        
        parser.add_argument('-b', '--backend', help='Choose the back end to emit the code (c is the default', type=str, choices=['c', 'python'])
        parser.add_argument('-d', '--dest-dir', help='destination directory for the generated code by default current directory is used.')
        parser.add_argument('-q', '--show-rewriting-equations', help='Show the rewriting equations for the given datalog program.',
                            action="store_true")
        parser.add_argument("-v", "--verbosity", type=str, choices=['minimum', 'info', 'debug'],
                                    help="set output verbosity default is info")
        parser.add_argument("-p", "--print-variables", help='indicate which variables, separated by commas, will be printed if not indicated all the intensional predicates will be printed')
        parser.add_argument("-r", "--decompose-program", type=str, choices=['left', 'right', 'random', 'common'], 
                            help='it takes the specified datalog program and generates a decomposed version of it')
        parser.add_argument("-n", "--no-code", help='option for debugging purposes, when activated doesn\'t emit source code',
                            action="store_true")
        parser.add_argument("-e", "--extensional", help='if the program has any predicate defined by the rules but it is also extensional use this option to specify it. ' +
                                                        'If there are more than one separate them by commas')

        # Process arguments
        args = parser.parse_args()
        
        # Check the verbosity
        if (args.verbosity == 'minimum'):
            logging_level = logging.WARNING
        elif (args.verbosity == 'debug'):
            logging_level = logging.DEBUG
        else:
            logging_level = logging.INFO
            
        # If we are going to show the rewriting equations we don't want to show any
        # logging information
        if args.show_rewriting_equations:
            logging_level = logging.CRITICAL
        
        # Specifing the options for the logging module
        logging.basicConfig(level=logging_level,
                            format="%(asctime)s %(levelname)s %(message)s",
                            datefmt="%Y-%m-%d %H:%M:%S")
        
        backend = 'c'
        if args.backend == 'python':
            backend = 'python'
        
        # Options for the pretty printer to work nicely
        # with the compiler defined types
        pp = pprint.PrettyPrinter(indent=3, depth=2)
        source_file = args.source_file[0]
                
        # Initialize the current directory to .
        # If we have defined another directory in the command options update it
        dest_dir='./'
        if args.dest_dir:
            dest_dir = args.dest_dir
            
        # Log the input filename and the destination directory
        # This goes to the info category
        logging.info("Filename:%s", source_file)
        logging.info("Destination Directory:%s", dest_dir)
        
        # Here we parse the predicate names provided by the command line
        # the predicates must be comma separated values.
        extensional_predicates_defined_by_rules = set()
        if args.extensional:
            extensional_predicates_defined_by_rules.update(args.extensional.split(','))
        
        # Check if we have to decompose the specified program
        # TODO: Add an option to choose the decomposition method
        if args.decompose_program:
            position = source_file.rfind(".")
            # TODO: Add an option to specify the decomposed filename
            dest_file = source_file[:position] + "-decomposed" + source_file[position:]
            logging.info("Decomposing {}".format(source_file))
            logging.info("Storing result at {}".format(dest_file))
            
            decomposedRules = decomposeRulesFromFile(source_file, args.decompose_program)
            saveDecomposedRules(decomposedRules, dest_file)
            
            # TODO: Should we continue with the execution here?
            sys.exit(0)
        
        # This is in charge of parsing the input file. As a reminder
        # After this point we only work with decomposed datalog programs
        # If the parser detects that it is not decomposed it will refuse
        # to continue. 
        # It returns several data structures. A table representing the Datalog 
        # program. It contains an entry in the table for every rule
        # of the Datalog program.
        # PredicateTypes gives information about the predicates which
        # are intensional and which extensional. This is not strictly
        # mandatory but helps to perform the computation later.
        # The dependencyGraph is a graph containing the predicate dependency
        # Of every rule in a bottom-up fashion
        rulesTable, predicateTypes, dependencyGraph, negatedPredicates = \
                buildRulesTable(source_file)
                
        # This function establishes the ordering for the different predicates
        # the algorithm is an optimization that imposes an scheduling to the
        # different variables to avoid some unnecessary operations. This 
        # function returns an ordering for the whole program, if we have more
        # than one stratum (we do this next). We have to split the ordering
        # for every stratum.
        ordering_for_blocks = predicateOrder(dependencyGraph, 
                                             predicateTypes.intensional,
                                             negatedPredicates)
        
        # This function is in charge of stratifying a program. The stratification is 
        # a technique used to handle logical programs that contains negated predicates
        # The functions returns a list that contains list of rules each of those lists
        # is a stratum, this stratums are also ordered, if one stratum is before another
        # in the list it has to be evaluated first. For example rules_per_stratum[0] will 
        # contain the rules that belong to the first stratum of a given program
        rules_per_stratum = stratifyRules(rulesTable)
        
        # stratums will contain the list of stratums. The definition of what is a Stratum
        # can be consulted at Types.py 
        stratums = []
        
        # This dictionary will contain as keys the identifiers of the rewriting
        # variables and as values the different stratums is present. It is consulted
        # to emit code. It is used for example when we fill the evalution queues of 
        # every stratum
        idToStratumLevels = defaultdict(set)
        
        # If the user specified the predicate names on the command line we have to convert
        # them here into identifiers. We do that by traversing the intensional predicates
        # set computed previously. Afterwards we have to update the previously computed 
        # extensional and intensional sets accordingly. 
        extensional_indentifiers = set()
        for extensional in extensional_predicates_defined_by_rules:
            for intensional in predicateTypes.intensional:
                if intensional.name == extensional:
                    extensional_indentifiers.add(intensional)
        extensional_predicates_defined_by_rules = extensional_indentifiers
        
        predicateTypes.extensional.update(extensional_predicates_defined_by_rules)
        predicateTypes.intensional.difference_update(extensional_predicates_defined_by_rules)
        
        # This section generates the stratums. The stratums will contain the rewriting 
        # equations and the different data required to build the views for the database. This is
        # generated by the rewritingEquationGenerator function. The rest of the code is used to
        # build the idToStratumLevels dictionary and the Ordering for the current stratum.
        # The code is a little bit bloated because the predicateOrder returns an Ordering for the
        # whole program and here we have to split it for every stratum
        for level, rules in enumerate(rules_per_stratum, start=1):
            # This function call is in charge of generating the set of rewriting equations.
            # It will return the equationsTable (a list) and the viewsData. In every row
            # of the equationsTable we have one of the required equations to obtain the 
            # solutions of the Datalog program. The ViewsData data structure (a named tuple
            # longer description in Types.py) contains information about how to perform the 
            # required operations (queries, navigations, etc...) using the data structure.
            # We could use comprehension lists to fill the different blocks but as we are 
            # filling more than one block it doesn't pay off.
            equationsTable, viewsData = rewritingEquationGenerator(rules)
            
            # Build the dictionary to establish the stratum level of the variables.
            # If we are in the first level we have to add to the block1 the predicates
            # specified by the user on the command line
            block1 = []
            if level == 1:
                block1 = list(extensional_predicates_defined_by_rules) 
            block2 = []; block3 = [] 
            for equation in equationsTable:
                idToStratumLevels[equation.leftVariable.id].add(level)
                
                # Check for the right side of the rules if we are in the last
                # stratum level they might not appear in another one.
                if level == len(rules_per_stratum):
                    idToStratumLevels[equation.rightVariable.id].add(level)
                
                # Check for negated predicates
                for negatedElement in equation.negatedElements:
                    idToStratumLevels[negatedElement.id].add(level)
                    
                    if negatedElement.id in ordering_for_blocks[0] and\
                       negatedElement.id not in block1:
                        block1.append(negatedElement.id)
                    
                # Here we have to contemplate if we are dealing with a negated
                # predicate in that case we have to reference it or otherwise
                # its values wont be stored on the database if the predicate
                # only appears as a negated predicate
                if equation.type == 2 and equation.consultingPredicate.negated and\
                      equation.consultingPredicate.id in ordering_for_blocks[0] and\
                      equation.consultingPredicate.id not in block1:
                    block1.append(equation.consultingPredicate.id)
                    
                # To add a variable we check that is the correct block
                # and that has not already been added as a variable. The variable
                # can appear in more than one equation and level. One optimization
                # would be use a set to check if a variable belongs to the block.
                if equation.leftVariable.id in ordering_for_blocks[0] and\
                     equation.leftVariable.id not in block1:
                    block1.append(equation.leftVariable.id)
                elif equation.leftVariable.id in ordering_for_blocks[1] and\
                     equation.leftVariable.id not in block2:
                    block2.append(equation.leftVariable.id)
                elif equation.leftVariable.id in ordering_for_blocks[2] and\
                     equation.leftVariable.id not in block3:
                    block3.append(equation.leftVariable.id)
                    
                if equation.rightVariable.id in ordering_for_blocks[0] and\
                   equation.rightVariable.id not in block1:
                    block1.append(equation.rightVariable.id)
                elif equation.rightVariable.id in ordering_for_blocks[1] and\
                     equation.rightVariable.id not in block2:
                    block2.append(equation.rightVariable.id)
                elif equation.rightVariable.id in ordering_for_blocks[2] and\
                     equation.rightVariable.id not in block3:
                    block3.append(equation.rightVariable.id)
    
            stratums.append(Stratum(equationsTable, viewsData, Ordering(block1, block2, block3)))
                
        # Here we have several pretty printers to show the different structures and other
        # interesting data computed so far from the given Datalog program in case the debug
        # option is requested by the user
        
        logging.debug("Generated dependency graph:")
        for var, key in dependencyGraph.iteritems():
            logging.debug('  %s -> %s', var, ", ".join([x.name for x in key.iterkeys()]))
            
        logging.debug("Rules table:")
        for rule in rulesTable:
            logging.debug("  " + pp.pformat(rule))
        
        for level, [equations, views, ordering] in enumerate(stratums, start=1):
            spaces = ""
            if len(stratums) > 1:
                logging.debug("STRATUM LEVEL " + str(level) + ":")
                spaces += "  "

            logging.debug(spaces + "Equations table:")
            for equation in equationsTable:
                logging.debug(spaces + "  " + pp.pformat(equations))
                
            logging.debug(spaces + "Views Data:")
            logging.debug(spaces + "  Views to Combinations:")
            for var, key in views.viewNamesToCombinations.iteritems():
                logging.debug(spaces + '    %s -> %s' % (var, str(key)))
                
            logging.debug(spaces + "  Alias to Combinations:")
            for var, key in views.aliasToViewNames.iteritems():
                logging.debug(spaces +  '    %s -> %s' % (var, key))
                
            logging.debug("  Predicates to viewNames:")
            for var, key in views.predsToViewNames.iteritems():
                logging.debug(spaces + '    %s -> %s' % (var, key))
                
            logging.debug("  Views ordering:")
            for view in views.viewsOrdering:
                logging.debug(spaces + "    " + str(view))
                
            logging.debug("Block order:")
            for block, ordering in enumerate(chain(ordering), start=1):
                logging.debug("  Block %i  -> %s", block, str(ordering))
                
        logging.debug("Identifiers To Stratum Levels:")
        for var, key in idToStratumLevels.iteritems():
            logging.debug("  %s -> %s" % (var, key))
            
        if args.show_rewriting_equations:
            for level, stratum in enumerate(stratums, start=1):
                if len(stratums) > 1:
                    print "STRATUM LEVEL " + str(level) + ":"
                rewritingEquationPrinter(stratum.equations)
            sys.exit()
                
        # --------- END OF THE DEBUGING INFORMATION -------------------- 
            
        # Here we control what information we provide to the standard output at the compiler
        # level without using the debuging option. If we don't provide anything nothing will
        # shown as output. This option is provided for a fast consult if we are only 
        # interested in the solutions of few predicates ideally one.
        # This may be is more complex than it should. We still save every solution for 
        # all the predicates in its respective files. The optimization to avoid storing 
        # the "temp" results is still to be implemented both in the respective file and in the
        # data structure
        if args.no_code == False:
            # Do not print anything to stdout by default
            printVariables = []
            #printVariables = predicateTypes.intensional
            if args.print_variables:
                printVariables = set(args.print_variables.split(','))
    
            # This function is in charge to generate the source code for a given
            # back-end. Currently only the C one is implemented. More planned
            # for the future.
            if backend == 'c':
                c_Backend.generate_code_from_template(dest_dir, stratums,
                                                  predicateTypes, predicateTypes.intensional,
                                                  printVariables, idToStratumLevels)
            else:
                py_Backend.generate_code_from_template(dest_dir, stratums,
                                                       predicateTypes, predicateTypes.intensional,
                                                       printVariables, idToStratumLevels)
            logging.info("Source code generated")
        
        
        return 0
    except KeyboardInterrupt:
        ### handle keyboard interrupt ###
        return 0
    except Exception, e:
        if DEBUG or TESTRUN:
            raise(e)
        indent = len(program_name) * " "
        sys.stderr.write(program_name + ": " + repr(e) + "\n")
        sys.stderr.write(indent + "  for help use --help")
        return 2

if __name__ == "__main__":
    if DEBUG:
        sys.argv.append("-h")
        #sys.argv.append("-v")
        #sys.argv.append("-r")
    if TESTRUN:
        import doctest
        doctest.testmod()
    if PROFILE:
        import cProfile
        import pstats
        profile_filename = 'dcompiler_profile.txt'
        cProfile.run('main()', profile_filename)
        statsfile = open("profile_stats.txt", "wb")
        p = pstats.Stats(profile_filename, stream=statsfile)
        stats = p.strip_dirs().sort_stats('cumulative')
        stats.print_stats()
        statsfile.close()
        sys.exit(0)
    sys.exit(main())
