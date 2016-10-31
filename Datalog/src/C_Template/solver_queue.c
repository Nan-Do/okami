%% fill_Header

#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "solver_queue.h"

void Queue_init(QueuePtr);
void Queue_free(QueuePtr);
bool Queue_empty(QueuePtr);
void Queue_append(QueuePtr, TYPE_REWRITING_VARIABLE *);
SolverNodePtr Queue_pop(QueuePtr);

void Queue_init(QueuePtr q){
    q->head = q->tail = NULL;
}

void Queue_free(QueuePtr q){
    SolverNodePtr t1, t2;
    
    for (t1 = q->head, t2 = q->head; t1; t2 = t2->next, t1 = t2 )
        free(t1);
}

bool Queue_empty(QueuePtr q){
    return (q->head == NULL);
}

void Queue_append(QueuePtr q, TYPE_REWRITING_VARIABLE *b){
    SolverNodePtr t;

    t = malloc(sizeof(SolverNode));
    /*memcpy((void *)&t->b, b, sizeof(TYPE_REWRITING_VARIABLE));*/
    t->b = *b;
    t->next = NULL;

    if (q->tail){
        q->tail->next = t;
        q->tail = t;
    }
    else{
        q->head = q->tail = t;
    }
}

SolverNodePtr Queue_pop(QueuePtr q){
    SolverNodePtr t = NULL;

    if (q->head){
        t = q->head;
        q->head = q->head->next;
    }
    
    return t;
}

void SolverQueue_init(SolverQueuePtr s){
    Queue_init(&s->q1);
    Queue_init(&s->q2);

    s->reading = &s->q1;
    s->writing = &s->q2;
}

void SolverQueue_free(SolverQueuePtr s){
    Queue_free(&s->q1);
    Queue_free(&s->q2);

    s->reading = s->writing = NULL;
}

void SolverQueue_append(SolverQueuePtr s, TYPE_REWRITING_VARIABLE *b){
    Queue_append(s->writing, b);
}

SolverNodePtr SolverQueue_pop(SolverQueuePtr s){
    QueuePtr temp_queue;
    SolverNodePtr t = NULL;

    /* Check if the reading queue is empty and
       switch the queues */
    if (Queue_empty(s->reading)){
        temp_queue = s->reading;
        s->reading = s->writing;
        s->writing = temp_queue;
        s->writing->tail = NULL;
    }

    t = Queue_pop(s->reading);

    return t;
}
