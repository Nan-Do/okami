#!/usr/local/bin/python2.7
# encoding: utf-8

import os, sys, glob
import logging
import subprocess
import shutil
import time

from itertools import chain

TMP_DIR = '/tmp'
COMPILER_NAME = 'dcompiler.py'

C_GENERATED_DIR = 'Solver_C_code'
C_COMPILED_FILENAME = 'solver'

PY_GENERATED_DIR = 'Solver_Py_code'
PY_COMPILER_NAME = 'main.py'

SHOW_SHELL = True

index = os.getcwd().rfind('/')
base_dir = os.getcwd()[:index]

Backends = ['C', 'Python']
Datalog_Examples = ['flights.datalog',
                    'graphClausure.dl',
                    'one-rule.dl',
                    'pointerAnalysis.dl',
                    'noCommonVars.dl',
                    'queens.dl',
                    'EqualCardsType1.dl',
                    'EqualCardsType2.dl',
                    'EqualCardsType2a.dl',
                    'EqualCardsType2b.dl',
                    'EqualCardsType2c.dl',
                    'EqualCardsType2d.dl',
                    'EqualCardsType2e.dl',
                    'EqualCardsType2f.dl',
                    'EqualCardsType2g.dl',
                    'example10.dl',
                    'example11.dl',
                    'example12.dl',
                    'example13.dl',
                    'example14.dl',
                    'example15.dl',
                    'example16.dl',
                    # Here start the examples that contain constant objects
                    'constants1.dl',
                    'constants2.dl',
                    'constants3.dl',
                    'constants4.dl',
                    'constants5.dl',
                    'constants6.dl',
                    'constants7.dl',
                    'constants8.dl',
                    'constants9.dl',
                    'constants10.dl',
                    'constants11.dl',
                    # Here start negated programs
                    'odds.dl',
                    'odds2.dl',
                    'negated.dl',
                    'negated2.dl',
                    'negated3.dl',
                    'negated4.dl',
                    'negated5.dl',
                    'negated6.dl',
                    'negated7.dl',
                    'negated8.dl',
                    'negated9.dl',
                    'twonegatedpredicates.dl',
                    # Programs with boolean expressions
                    'booleanOneRule.dl',
                    'booleanOneRuleExpression.dl',
                    'booleanOneRuleExpression2.dl',
                    'booleanOneRuleExpression3.dl',
                    'booleanCanReach.dl',
                    'booleanCanReach2.dl',
                    'booleanTwoRules.dl',
                    'booleanTwoRules2.dl',
                    'booleanTwoExpressions.dl',
                    'booleanOneRuleExpression4.dl',
                    'booleanOneRuleExpression5.dl',
                    'booleanOneRuleExpression6.dl',
                    'odds-restricted.dl',
                    # Programs including negation
                    'negation-boolean.dl',
                    'negationTwoPredicates.dl',
                    'negationTwoPredicates2.dl',
                    'negationTwoPredicates3.dl',
                    'negationTwoPredicates4.dl',
                    'negationTwoPredicates5.dl',
                    # Programs with assignation expressions
                    'assignation1.dl',
                    'assignation2.dl',
                    'assignation3.dl',
                    'assignation4.dl',
                    'assignation5.dl',
                    'assignation6.dl',
                    'assignation7.dl',
                    'assignation8.dl'
                    ]

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s",
                    datefmt="%Y-%m-%d %H:%M:%S")


for backend in Backends:
    BACKEND = ''
    
    if backend == 'C':
        GENERATED_DIR = C_GENERATED_DIR
        COMPILED_FILENAME = C_COMPILED_FILENAME
        BACKEND = ' -b c'
    else:
        GENERATED_DIR = PY_GENERATED_DIR
        COMPILED_FILENAME = PY_COMPILER_NAME
        BACKEND = ' -b python'
        
    # Create the directories
    os.chdir(base_dir)
    compiler_dir = os.path.join(base_dir, 'src')
    solver_dir = os.path.join(TMP_DIR, GENERATED_DIR)
    
    for example in Datalog_Examples:
        # If the solver directory exists remove it
        if os.path.exists(solver_dir):
            shutil.rmtree(solver_dir)
    
        # Change to the compiler directory and generate the solver for the given
        # program
        os.chdir(compiler_dir)
        logging.info("Emitting code for: " + example)
        command = 'python ' + COMPILER_NAME + BACKEND + ' -d ' + TMP_DIR + ' ../examples/' + example
        subprocess.call(command, shell=SHOW_SHELL)
        if os.path.isdir(solver_dir):
            logging.info("Code emitted successfully")
        else:
            logging.error("Code not emitted.")
            logging.error("EXITING")
            sys.exit()
    
        # Change to the solver directory, compile it and check that the solver was
        # created
        os.chdir(solver_dir)
        if backend == 'C':
            logging.info("Compiling the source code")
            subprocess.call('make', shell=SHOW_SHELL)
            if os.path.exists(os.path.join(solver_dir, COMPILED_FILENAME)):
                logging.info('Compiled successfully')
            else:
                logging.info('Compilation failed')

    
        # Copy the input files, execute the solver and check we got the correct
        # answers
        logging.info('Copying the files into compiler directory')
        data_dir = os.path.join(base_dir, 'examples', example.split('.')[0])
        input_files =  glob.glob(os.path.join(data_dir, '*.input'))
        output_files =  glob.glob(os.path.join(data_dir, '*.output'))
        answer_names = []
        for pos, src in enumerate(chain(input_files, output_files)):
            name =  os.path.basename(src).split('.')[0]
            chunk = '.tuples'
            if pos >= len (input_files):
                chunk = '-CorrectAnswer.tuples'
                answer_names.append(name)
            dst = os.path.join(solver_dir, name + chunk)
            shutil.copy(src, dst)
        logging.info('Files copied')
        logging.info('Executing the solver')
        #subprocess.call('./solver', shell=SHOW_SHELL)
        if backend == 'C':
            subprocess.call('./solver', shell=SHOW_SHELL)
        else:
            subprocess.call('python main.py', shell=SHOW_SHELL)
            
        logging.info('Solver finished')
        logging.info('Checking that the answers are correct')
    
        # Compare the results with the results that should be obtained
        for answer in answer_names:
            if not os.path.exists(answer + '.tuples'):
                logging.error(answer + '.tuples not generated properly')
                logging.error("EXITING")
                sys.exit()
            subprocess.Popen(['sort', answer + '.tuples', '-o' + answer + '.tuples'])
            time.sleep(0.01)
            #subprocess.Popen(['sort', answer + '-CorrectAnswer.tuples', '-o' + answer + '-CorrectAnswer.tuples'])
            #time.sleep(0.01)
            p = subprocess.Popen(['diff', answer + '.tuples', answer + '-CorrectAnswer.tuples'], stdout=subprocess.PIPE)
    
            if p.stdout.read():
                logging.error(answer + '.tuples doesn\'t contain the proper answers')
                sys.exit()
    
        logging.info('Generated answers are correct')
        logging.info('FINISHED\n')
    
    
