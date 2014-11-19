#!/usr/local/bin/python2.7
# encoding: utf-8

import os, shutil
import logging, time
import subprocess

REPETITIONS = 1

TMP_DIR = '/tmp'
RESULTS = 'Datalog_Experiments_Results'
GENERATED_DIR = 'Solver_C_code'
COMPILER_NAME = 'dcompiler.py'
COMPILED_FILENAME = 'solver'

SCRIPT_DIR = os.getcwd()
BASE_DIR = os.getcwd()[:os.getcwd().rfind('/')]
COMPILER_DIR = os.path.join(BASE_DIR, "src")
EXPERIMENTS_DIR = os.path.join(TMP_DIR, RESULTS)
FAKE_DATA_GENERATOR = "FakeDataPredicatePopulator.py"

DEVNULL = open(os.devnull, 'wb')



# Here we colect the data of the datalog program examples we want to measure first we have the file name
# it must be located in the examples directory, second the predicate we want to track, third its length
# and forth the sizes of the fake data that will be generated
Datalog_Examples = [ #('siblings.dl', 'sibling', 2, [ 500, 1000, 2000, 4000, 8000, 16000, 32000, 64000, 128000, 256000 ], 4000, None),
                     #('family.dl', 'brother', 2, [ 500, 1000, 2000, 4000, 8000, 16000, 32000, 64000, 128000 ], 2500, None),
                     ('pointerAnalysis.dl', 'vP', 2, [ 500, 1000, 2000, 4000, 8000, 16000], 10000, 'a:0.55,vP0:0.45,st:0.025,ld:0.025' )
                   ]


logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s",
                    datefmt="%Y-%m-%d %H:%M:%S")

# Check if the directory in which we will store the experiments data exists if it exists remove it
def create_new_directory(directory):
    if os.path.exists(directory):
        shutil.rmtree(directory)
    os.makedirs(directory)

# Run the experiments REPITITIONS times and return the average time
def collect_experiments_average_time(command):
    timedeltas = []

    for _ in xrange(REPETITIONS):
        start = time.time()
        os.system(command)
        end = time.time()
        timedeltas.append(end - start)

    average_timedelta = sum(timedeltas) / len(timedeltas)
    return average_timedelta


def run_prototype(sizes, base_data_directory, experiment_directory, file_name, predicate_name):
    current_dir = os.getcwd()
    working_directory = os.path.join(experiment_directory, "prototype")

    # Create the solver
    os.chdir(COMPILER_DIR)
    command = ['python', COMPILER_NAME, '-d', working_directory, '../examples/' + file_name]
    subprocess.call(command, stdout=DEVNULL)
    os.chdir(os.path.join(working_directory, GENERATED_DIR))
    subprocess.call(['make'], stdout=DEVNULL)
    subprocess.call(['mv', 'solver', '../'], stdout=DEVNULL)

    # Execute the solver and collect the times
    times = open(os.path.join(working_directory, 'solutions.dat'), 'w')
    times.write('INPUT FACTS\tSOLUTIONS\tTIME\tSOLUTIONS PER SECOND\n')
    print "Prototype"
    for size in sizes:
        os.makedirs(os.path.join(os.path.join(working_directory, str(size))))
        os.chdir(os.path.join(working_directory, str(size)))
        os.system('ln -s ' + os.path.join(base_data_directory, str(size), '*') + ' ./')

        time_average = collect_experiments_average_time('../solver')

        num_of_solutions = subprocess.check_output(['wc', '-l', predicate_name + '.tuples']).split()[0]
        print file_name, size, num_of_solutions, time_average, float(num_of_solutions)/time_average
        times.write("{}\t\t{}\t\t{}\t\t{}\n".format(str(size),
                                                    num_of_solutions,
                                                    str(time_average),
                                                    str(float(num_of_solutions)/time_average)))
    times.close()
    os.chdir(current_dir)

def run_yap(sizes, base_data_directory, experiment_directory, file_name, predicate_name, predicate_length):
    current_dir = os.getcwd()
    working_directory = os.path.join(experiment_directory, "yap_prolog")
    create_new_directory(working_directory)
    os.system('cp ' + BASE_DIR + '/examples/' + file_name + ' ' + working_directory)

    # Execute the solver and collect the times
    times = open(os.path.join(working_directory, 'solutions.dat'), 'w')
    times.write('INPUT FACTS\tSOLUTIONS\tTIME\tSOLUTIONS PER SECOND\n')
    print "Yap prolog"
    for size in sizes:
        os.makedirs(os.path.join(os.path.join(working_directory, str(size))))
        os.chdir(os.path.join(working_directory, str(size)))
        os.system('cat ' + os.path.join(base_data_directory, str(size), '*') + ' > ' + file_name.split('.')[0] + '.pl')
        os.system('cat ' + '../' + file_name + ' >>' + file_name.split('.')[0] + '.pl')

        # Create the run file
        t = open('run.pl', 'w')
        t.write('[ {} ].\n'.format(file_name.split('.')[0]))
        #t.write('table {}/{}.'.format(predicate_name, predicate_length))
        var_names = ', '.join([ 'X' + str(x) for x in xrange(1, predicate_length + 1)])
        t.write('all( ({}), {}({}), Solutions).\n'.format(var_names, predicate_name, var_names))
        t.close

        # Create the running script
        t = open('run.sh', 'w')
        t.write('yap < run.pl 2> /dev/stdout | tail -n 1 > solutions.txt')
        t.close()

        # Run the experiments
        time_average = collect_experiments_average_time('sh run.sh')

        num_of_solutions = subprocess.check_output('cat solutions.txt | sed -e "s/),(/\\n/g" | tr -d "()][Solutions= " | uniq | wc -l', shell=True)[:-1]

        print file_name, size, num_of_solutions, time_average, float(num_of_solutions)/time_average
        times.write("{}\t\t{}\t\t{}\t\t{}\n".format(str(size),
                                                    num_of_solutions,
                                                    str(time_average),
                                                    str(float(num_of_solutions)/time_average)))
    times.close()
    os.chdir(current_dir)

def run_xsb(sizes, base_data_directory, experiment_directory, file_name, predicate_name, predicate_length):
    current_dir = os.getcwd()
    working_directory = os.path.join(experiment_directory, "xsb_prolog")
    create_new_directory(working_directory)
    os.system('cp ' + BASE_DIR + '/examples/' + file_name + ' ' + working_directory)

    # Execute the solver and collect the times
    times = open(os.path.join(working_directory, 'solutions.dat'), 'w')
    times.write('INPUT FACTS\tSOLUTIONS\tTIME\tSOLUTIONS PER SECOND\n')
    print "XSB prolog"
    for size in sizes:
        os.makedirs(os.path.join(os.path.join(working_directory, str(size))))
        os.chdir(os.path.join(working_directory, str(size)))
        os.system('cat ' + os.path.join(base_data_directory, str(size), '*') + ' > ' + file_name.split('.')[0] + '.pl')
        os.system('cat ' + '../' + file_name + ' >>' + file_name.split('.')[0] + '.pl')

        # Create the run file
        t = open('run.pl', 'w')
        t.write('[ {} ].\n'.format(file_name.split('.')[0]))
        var_names = ', '.join([ 'X' + str(x) for x in xrange(1, predicate_length + 1)])
        t.write('findall( [{}], {}({}), Solutions).\n'.format(var_names, predicate_name, var_names))
        t.close

        # Create the running script
        t = open('run.sh', 'w')
        t.write('/home/nando/Downloads/XSB/bin/xsb < run.pl 2> /dev/null | tail -n 3 | head -n 1 > solutions.txt')
        t.close()

        # Run the experiments
        time_average = collect_experiments_average_time('sh run.sh')

        # Collect the number of solutions
        num_of_solutions = subprocess.check_output('cat solutions.txt | sed "s/\],\[/\\n/g" | tr -d "][Solutions= " | sort | uniq | wc -l', shell=True)[:-1]

        print file_name, size, num_of_solutions, time_average, float(num_of_solutions)/time_average
        times.write("{}\t\t{}\t\t{}\t\t{}\n".format(str(size),
                                                    num_of_solutions,
                                                    str(time_average),
                                                    str(float(num_of_solutions)/time_average)))
    times.close()
    os.chdir(current_dir)



# Check if the experiments directory exists
create_new_directory(EXPERIMENTS_DIR)

for file_name, predicate_name, predicate_length, sizes, domain_size, tuples_proportions in Datalog_Examples:
    experiment_directory = os.path.join(EXPERIMENTS_DIR, file_name.split('.')[0])
    create_new_directory(experiment_directory)
    os.system('cp ' + SCRIPT_DIR + '/generate_graph.sh' + ' ' + experiment_directory )
    base_data_directory = os.path.join(experiment_directory, "Data")
    logging.info("Generating data for: " + file_name)
    os.chdir(COMPILER_DIR)
    for size in sizes:
        size_directory = os.path.join(base_data_directory, str(size))
        create_new_directory(size_directory)
        if not tuples_proportions:
            command = ['python', FAKE_DATA_GENERATOR, '-d', size_directory, '-s', str(domain_size),  '-n', str(size), '../examples/' + file_name ]
        else:
            command = ['python', FAKE_DATA_GENERATOR, '-d', size_directory, '-s', str(domain_size),  '-n', str(size), '-p', tuples_proportions, '../examples/' + file_name ]
        subprocess.call(command, stdout=DEVNULL)

    run_prototype(sizes, base_data_directory, experiment_directory, file_name, predicate_name)
    run_xsb(sizes, base_data_directory, experiment_directory, file_name, predicate_name, predicate_length)
    run_yap(sizes, base_data_directory, experiment_directory, file_name, predicate_name, predicate_length)

    # Generate the graph
    os.chdir(experiment_directory)
    os.system('sh generate_graph.sh')
    logging.info('Generated graph for ' + file_name.split('.')[0])


