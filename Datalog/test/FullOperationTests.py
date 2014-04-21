#!/usr/local/bin/python2.7
# encoding: utf-8

import os, sys, glob
import logging
import subprocess
import shutil

from itertools import chain

TMP_DIR = '/tmp'
GENERATED_DIR = 'Solver_C_code'
COMPILER_NAME = 'dcompiler.py'
COMPILED_FILENAME = 'solver'
SHOW_SHELL = True

Datalog_Examples = ['flights.datalog',
                    'graphClausure.dl',
                    'one-rule.dl',
                    'pointerAnalysis.dl',
                    'noCommonVars.dl',
                    'EqualCardsType1.dl',
                    'EqualCardsType2.dl',
                    'EqualCardsType2a.dl',
                    'EqualCardsType2b.dl',
                    'EqualCardsType2c.dl',
                    'EqualCardsType2d.dl',
                    'EqualCardsType2e.dl',
                    'EqualCardsType2f.dl',
                    'example10.dl',
                    'example11.dl',
                    ]

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s",
                    datefmt="%Y-%m-%d %H:%M:%S")

# Create the directories
index = os.getcwd().rfind('/')
base_dir = os.getcwd()[:index]
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
    command = 'python ' + COMPILER_NAME + ' -d ' + TMP_DIR + ' ../examples/' + example
    subprocess.call(command, shell=SHOW_SHELL)
    if os.path.isdir(solver_dir):
        logging.info("Code emitted successfully")
    else:
        logging.error("Code not emitted.")
        logging.error("EXITING")
        sys.exit()
        
    # Change to the solver directory, compile it and check that the solver was 
    # created
    logging.info("Compiling the source code")
    os.chdir(solver_dir)
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
    subprocess.call('./solver', shell=SHOW_SHELL)
    logging.info('Solver finished')
    logging.info('Checking that the answers are correct')
    
    # Compare the results with the results that should be obtained
    for answer in answer_names:
        if not os.path.exists(answer + '.tuples'):
            logging.error(answer + '.tuples not generated properly')
            logging.error("EXITING")
            sys.exit()
        p = subprocess.Popen(['diff', answer + '.tuples', answer + '-CorrectAnswer.tuples'], stdout=subprocess.PIPE)
        
        if p.stdout.read():
            logging.error(answer + '.tuples doesn\'t contain the proper answers')
            sys.exit()
            
    logging.info('Generated answers are correct')
    logging.info('FINISHED\n')
        
        
