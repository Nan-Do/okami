#!/usr/local/bin/python2.7
# encoding: utf-8

import os
import sys
import subprocess

TMP_DIR = '/tmp'
GENERATED_DIR = 'Solver_C_code'
COMPILED_FILENAME = 'solver'
SHOW_SHELL = True

Examples = ['flights.datalog']

# Get the base directory
index = os.getcwd().rfind('/')
working_dir = os.getcwd()[:index] + '/src' 

for example in Examples:
    os.chdir(working_dir)
    print "GENERATING: " + example
    command = 'python main.py -d ' + TMP_DIR + ' ../examples/' + example
    subprocess.call(command, shell=SHOW_SHELL)
    if os.path.isdir(TMP_DIR + '/' + GENERATED_DIR):
        print "CODE GENERATED SUCCESFULLY"
    else:
        print "CODE NOT GENERATED SUCCESFULLY."
        print "EXITING"
        sys.exit()
        
    print "COMPILING THE SOURCE CODE"
    os.chdir(TMP_DIR + '/' + GENERATED_DIR)
    subprocess.call('make', shell=SHOW_SHELL)
    if os.path.exists(TMP_DIR + '/' + GENERATED_DIR + '/' + COMPILED_FILENAME):
        print 'COMPILED SUCCESFULLY'
    else:
        print 'COMPILATION FAILED'
