%% fill_Header

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "solver.h"
#include "parser.h"
#include "fact.h"
#include "utils.h"
#include "data_structure.h"
#include "solver_queue.h"

%% fill_InputTuplesFiles

%% fill_OutputTuplesFiles

/* SolverQueue solver; */
%% fill_StratumSolverQueues

/* Functions to print the data */
void print_rewriting_variable(FILE *, TYPE_REWRITING_VARIABLE *);
void print_answer(FILE *file, TYPE_REWRITING_VARIABLE *b);

void print_rewriting_variable(FILE *file, TYPE_REWRITING_VARIABLE *b){
%% fill_PrintRewritingVariable
}

void print_answer(FILE *file, TYPE_REWRITING_VARIABLE *b){
%% fill_PrintAnswer
}

int solver_init(){
    Ds_init();

%% fill_SolverInit

    return true;
}

%% fill_StratumQueueInitializers

int solver_compute(){
%% fill_IntList
    SolverNodePtr current;
    TYPE_REWRITING_VARIABLE VAR;

%% fill_SolverCompute

    return true;
}

void solver_free(){
%% fill_SolverFree
}
