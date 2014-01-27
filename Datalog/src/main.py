#! /usr/bin/python

'''
Created on Jul 26, 2013

@author: nando
'''

import pprint
import argparse
import sys
import logging

from BuildRulesTable import buildRulesTable
from GenerateRules import generateRules, printRewritingEquations
from PredicateOrder import predicateOrder
from c_Backend import generate_code_from_template

if __name__ == '__main__':
    dest_dir='./'
    
    parser = argparse.ArgumentParser(description='Compiler for datalog.')
    parser.add_argument('source_file', metavar='file.datalog', type=str, nargs=1,
                   help='The datalog program to compile')
    
    parser.add_argument('-d', '--dest-dir', help='destination directory for the generated code by default current directory is used.')
    parser.add_argument('-e', '--show-rewriting-equations', help='Show the rewriting equations for the given datalog program.',
                        action="store_true")
    parser.add_argument("-v", "--verbosity", type=str, choices=['minimum', 'info', 'debug'],
                                help="set output verbosity default is info")
    parser.add_argument("-p", "--print-variables", help='indicate which variables, separated by commas, will be printed if not indicated all the intensional predicates will be printed')
    parser.add_argument("-n", "--no-code", help='option for debugging purposes, when activated doesn\'t emit source code',
                        action="store_true")
    
    args = parser.parse_args()
    
    if (args.verbosity == 'minimum'):
        logging.basicConfig(level=logging.WARNING)
    elif (args.verbosity == 'debug'):
        logging.basicConfig(level=logging.DEBUG)
    else:
        logging.basicConfig(level=logging.INFO)
    
    pp = pprint.PrettyPrinter(indent=3, depth=2)
    source_file = args.source_file[0]
            
    if args.dest_dir:
        dest_dir = args.dest_dir
        
    logging.info("Filename:%s", source_file)
    logging.info("Destination Directory:%s", dest_dir)
    
    # Get the equations table
    rulesTable, predicateTypes, dependencyGraph = \
            buildRulesTable(source_file)
            
    equationsTable, viewsData = generateRules(rulesTable)
    
    logging.debug("Generated dependency graph:")
    #logging.debug(pp.pformat(dependencyGraph))
    for var, key in dependencyGraph.iteritems():
        logging.debug('  %s -> %s', var, ", ".join([x for x in key.iterkeys()]))
        
    logging.debug("Rules table:")
    for rule in rulesTable:
        logging.debug("  " + pp.pformat(rule))
        
    logging.debug("Equations table:")
    #logging.debug(pp.pformat(equationsTable))
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
        
    #print 'Views data:'
    
    #print '  View viewNames to Combinations:'
    #pp.pprint(viewsData.viewNamesToCombinations)
    #print '\n  View alias to ViewNames:'
    #pp.pprint(viewsData.aliasToViewNames)
    #print '\n  View Predicates to ViewNames:'
    #pp.pprint(viewsData.predsToViewNames)
    #print '\n  View ordering:'
    #pp.pprint(viewsData.viewsOrdering)
    
    #print '\nRewriting equations data structure: '
    #pp.pprint(equationsTable)
    
    #print '\n\nRewriting equations:'
    #printRewritingEquations(equationsTable)
    
    #print '\nExtensional predicates: ' + ", ".join(predicateTypes.extensional) + '.'
    #print 'Intensional predicates: ' + ", ".join(predicateTypes.intensional) + '.'
    
    #print '\nDependency Graph:'
    #pp._indent_per_level = 2
    #pp.pprint(dependencyGraph)

    ordering_for_blocks = predicateOrder(dependencyGraph)
    #ordering_for_blocks[0].append('A')
        
    logging.debug("Block order:")
    for block, ordering in enumerate(ordering_for_blocks, start=1):
        logging.debug("  Block %i  -> %s", block, str(ordering))
        
    if args.no_code == False:
        # Do not print anything to stdout by default
        printVariables = []
        #printVariables = predicateTypes.intensional
        if args.print_variables:
            printVariables = set(args.print_variables.split(','))

        generate_code_from_template(dest_dir, equationsTable, viewsData,
                                    predicateTypes, ordering_for_blocks,
                                    predicateTypes.intensional, printVariables)
        logging.info("Source code generated")
            
    