%% fill_Header

#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "solver_queue.h"

void SolverQueue_init(QueuePtr q){
    q->head = q->tail = NULL;
}

void SolverQueue_free(QueuePtr q){
    SolverNodePtr t1, t2;
    
    for (t1 = q->head, t2 = q->head; t1; t2 = t2->next, t1 = t2 )
        free(t1);
}

void SolverQueue_append(QueuePtr q, TYPE_REWRITING_VARIABLE *b){
    SolverNodePtr t;

    t = malloc(sizeof(SolverNode));
    memcpy((void *)&t->b, b, sizeof(TYPE_REWRITING_VARIABLE));
    /*t->b = *b;*/
    t->next = NULL;

    if (q->tail){
        q->tail->next = t;
        q->tail = t;
    }
    else{
        q->head = q->tail = t;
    }
}

SolverNodePtr SolverQueue_pop(QueuePtr q){
    SolverNodePtr t = NULL;

    if (q->head){
        t = q->head;
        q->head = q->head->next;
    }
    
    return t;
}
