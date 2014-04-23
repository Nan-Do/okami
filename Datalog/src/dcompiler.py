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

from argparse import ArgumentParser
from argparse import RawDescriptionHelpFormatter

# Compiler code imports
from BuildRulesTable import buildRulesTable
from RuleDecomposer import decomposeRulesFromFile, saveDecomposedRules
from GenerateRules import generateRules, printRewritingEquations
from PredicateOrder import predicateOrder
from c_Backend import generate_code_from_template

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
        
        parser.add_argument('-d', '--dest-dir', help='destination directory for the generated code by default current directory is used.')
        parser.add_argument('-e', '--show-rewriting-equations', help='Show the rewriting equations for the given datalog program.',
                            action="store_true")
        parser.add_argument("-v", "--verbosity", type=str, choices=['minimum', 'info', 'debug'],
                                    help="set output verbosity default is info")
        parser.add_argument("-p", "--print-variables", help='indicate which variables, separated by commas, will be printed if not indicated all the intensional predicates will be printed')
        parser.add_argument("-r", "--decompose-program", type=str, choices=['left', 'right', 'random', 'common'], 
                            help='it takes the specified datalog program and generates a decomposed version of it')
        parser.add_argument("-n", "--no-code", help='option for debugging purposes, when activated doesn\'t emit source code',
                            action="store_true")

        # Process arguments
        args = parser.parse_args()
        
        # Check the verbosity
        if (args.verbosity == 'minimum'):
            logging_level = logging.WARNING
        elif (args.verbosity == 'debug'):
            logging_level = logging.DEBUG
        else:
            logging_level = logging.INFO
            
        # Specifing the options for the logging module
        logging.basicConfig(level=logging_level,
                            format="%(asctime)s %(levelname)s %(message)s",
                            datefmt="%Y-%m-%d %H:%M:%S")
        
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
        
        # Check if we have to decompose the specified program
        # TODO: Add an option to choose the decomposition method
        if args.decompose_program:
            pos = source_file.rfind(".")
            # TODO: Add an option to specify the decomposed filename
            dest_file = source_file[:pos] + "-decomposed" + source_file[pos:]
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
        rulesTable, predicateTypes, dependencyGraph = \
                buildRulesTable(source_file)
                
        # This function call is in charge of generating the set of rewriting equations.
        # It will return the equationsTable (a list) and the viewsData. In every row
        # of the equationsTable we have one of the required equations to obtain the 
        # solutions of the Datalog program. The ViewsData data structure (a named tuple
        # longer description in utils.py) contains information about how to perform the 
        # required operations (queries, navigations, etc...) using the data structure.
        equationsTable, viewsData = generateRules(rulesTable)
        
        # This function establishes the ordering for the different predicates
        # the algorithm is an optimization that imposes an scheduling to the
        # different variables to avoid some unnecessary operations
        ordering_for_blocks = predicateOrder(dependencyGraph, predicateTypes.intensional)
        
        # Here we have several pretty printers to show the different structures and other
        # interesting data computed so far from the given Datalog program in case the debug
        # option is requested by the user
        # TODO: Improve the logging output information 
        logging.debug("Generated dependency graph:")
        for var, key in dependencyGraph.iteritems():
            logging.debug('  %s -> %s', var, ", ".join([x for x in key.iterkeys()]))
            
        logging.debug("Rules table:")
        for rule in rulesTable:
            logging.debug("  " + pp.pformat(rule))
            
        logging.debug("Equations table:")
        for equation in equationsTable:
            logging.debug("  " + pp.pformat(equation))
            
        logging.debug("Views Data:")
        logging.debug("  Views to Combinations:")
        for var, key in viewsData.viewNamesToCombinations.iteritems():
            logging.debug('    %s -> %s', var, str(key))
            
        logging.debug("  Alias to Combinations:")
        for var, key in viewsData.aliasToViewNames.iteritems():
            logging.debug('    %s -> %s', var, key)
            
        logging.debug("  Predicates to viewNames:")
        for var, key in viewsData.predsToViewNames.iteritems():
            logging.debug('    %s -> %s', var, key)
            
        logging.debug("  Views ordering:")
        for view in viewsData.viewsOrdering:
            logging.debug("    " + str(view))
        
        if args.show_rewriting_equations:
            printRewritingEquations(equationsTable)
            sys.exit()
            
        logging.debug("Block order:")
        for block, ordering in enumerate(ordering_for_blocks, start=1):
            logging.debug("  Block %i  -> %s", block, str(ordering))
            
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
            generate_code_from_template(dest_dir, equationsTable, viewsData,
                                        predicateTypes, ordering_for_blocks,
                                        predicateTypes.intensional, printVariables)
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
