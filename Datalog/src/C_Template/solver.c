%% fill_Header

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "solver.h"
#include "parser.h"
#include "fact.h"
#include "utils.h"
#include "data_structure.h"

%% fill_InputTuplesFiles

%% fill_OutputTuplesFiles

struct SolverNode{
	TYPE_REWRITING_VARIABLE b;
	struct SolverNode *next;
};
typedef struct SolverNode SolverNode;
typedef struct SolverNode *SolverNodePtr;

struct SolverQueue{
	SolverNodePtr head, tail;
};
typedef struct SolverQueue SolverQueue;

void SolverQueue_init(SolverQueue *);
void SolverQueue_free(SolverQueue *);

void SolverQueue_append(SolverQueue *, TYPE_REWRITING_VARIABLE *);

/* SolverQueue solver; */
%% fill_StratumSolverQueues
unsigned long count=0;

/* Functions to print the data */
void print_rewriting_variable(FILE *, TYPE_REWRITING_VARIABLE *);
void print_answer(FILE *file, TYPE_REWRITING_VARIABLE *b);

void SolverQueue_init(SolverQueue *s){
    s->head = s->tail = NULL;
}

void SolverQueue_free(SolverQueue *s){
    SolverNodePtr t1, t2;
    for (t1 = s->head, t2 = s->head; t1; t2 = t2->next, t1 = t2 )
        free(t1);
}

void SolverQueue_append(SolverQueue *s, TYPE_REWRITING_VARIABLE *b){
    SolverNodePtr t;

    t = malloc(sizeof(SolverNode));
    /*memcpy((void *)&t->b, b, sizeof(TYPE_REWRITING_VARIABLE));*/
    t->b = *b;
    t->next = NULL;

    if (s->tail){
        s->tail->next = t;
        s->tail = t;
    }
    else{
        s->head = s->tail = t;
    }
    count++;
}

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
