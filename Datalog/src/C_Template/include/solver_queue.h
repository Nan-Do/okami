%% fill_Header

#include <stdio.h>

#include "solver.h"

#ifndef SOLVER_QUEUE_H_
#define SOLVER_QUEUE_H_

struct SolverNode{
	TYPE_REWRITING_VARIABLE b;
	struct SolverNode *next;
};
typedef struct SolverNode SolverNode;
typedef struct SolverNode *SolverNodePtr;

struct Queue{
	SolverNodePtr head, tail;
};
typedef struct Queue Queue;
typedef struct Queue * QueuePtr;
typedef struct Queue SolverQueue;
typedef struct Queue * SolverQueuePtr;

extern void SolverQueue_init(SolverQueuePtr);
extern void SolverQueue_free(SolverQueuePtr);
extern void SolverQueue_append(SolverQueuePtr, TYPE_REWRITING_VARIABLE *);
extern SolverNodePtr SolverQueue_pop(SolverQueuePtr);

#endif
