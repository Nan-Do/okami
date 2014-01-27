/*
 * solver.h
 *
 * Created by: C Code Generator
 * Created on: 2014-01-21
 */

#ifndef SOLVER_H_
#define SOLVER_H_

struct STRUCT_REWRITING_VARIABLE {
	unsigned char PREDICATE;

	unsigned int VAR_1;
	unsigned int VAR_2;
	unsigned int VAR_3;
	unsigned int VAR_4;
	unsigned int VAR_5;
};
typedef struct STRUCT_REWRITING_VARIABLE TYPE_REWRITING_VARIABLE;

extern int solver_init();
extern int solver_compute();
extern void solver_free();
extern void solver_print_solution(FILE *);

#endif
