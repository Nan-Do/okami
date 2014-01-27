/*
 * solver.c
 *
 * Created by: C Code Generator
 * Created on: 2014-01-21
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "solver.h"
#include "parser.h"
#include "fact.h"
#include "utils.h"
#include "data_structure.h"
#include "mem.h"

static char *tuples_input_files[] = {
	"Flights.tuples"
};
#define INPUT_TUPLES_FILES 1

static char *tuples_output_files[] = {
	"Reaches.tuples"
};
#define OUTPUT_TUPLES_FILES 1
FILE *fp_Reaches;

struct SolverNode{
	TYPE_REWRITING_VARIABLE b;
	struct SolverNode *next;
};
typedef struct SolverNode *SolverNode;

struct SolverQueue{
	SolverNode head, tail;
};
typedef struct SolverQueue SolverQueue;

void SolverQueue_init(SolverQueue *);
void SolverQueue_free(SolverQueue *);

void SolverQueue_append(SolverQueue *, TYPE_REWRITING_VARIABLE *);

SolverQueue solver;
unsigned long count=0;

/* Functions to print the data */
void print_rewriting_variable(FILE *, TYPE_REWRITING_VARIABLE *);
void print_answer(FILE *file, TYPE_REWRITING_VARIABLE *b);

void SolverQueue_init(SolverQueue *s){
	s->head = s->tail = NULL;
}

void SolverQueue_free(SolverQueue *s){
	SolverNode t1, t2;
	for (t1 = s->head, t2 = s->head; t1; t2 = t2->next, t1 = t2 )
		FREE(t1);
}

void SolverQueue_append(SolverQueue *s, TYPE_REWRITING_VARIABLE *b){
	SolverNode t;

	NEW(t);
	memcpy((void *)&t->b, b, sizeof(TYPE_REWRITING_VARIABLE));
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
	if (b->PREDICATE == Flights)
		fprintf(file, "X_Flights(%i, %i, %i, %i, %i).", b->VAR_1, b->VAR_2, b->VAR_3, b->VAR_4, b->VAR_5);
	else if (b->PREDICATE == Reaches)
		fprintf(file, "X_Reaches(%i, %i).", b->VAR_1, b->VAR_2);
}

void print_answer(FILE *file, TYPE_REWRITING_VARIABLE *b){
	if (b->PREDICATE == Flights)
		fprintf(file, "Flights(%i, %i, %i, %i, %i).\n", b->VAR_1, b->VAR_2, b->VAR_3, b->VAR_4, b->VAR_5);
	else if (b->PREDICATE == Reaches)
		fprintf(file, "Reaches(%i, %i).\n", b->VAR_1, b->VAR_2);
}

int solver_init(){
	FILE *fp;
	Fact fact;
	TYPE_REWRITING_VARIABLE VAR;

	Mem_init();
	Ds_init();
	SolverQueue_init(&solver);

	/* Fill SolverQueue with facts from files */
	fp = fopen(tuples_input_files[0], "r");
	if (!fp){
		fprintf(stderr, "Error: Can't open file %s\n", tuples_input_files[0]);
		return FALSE;
	}
	while (parser_get_fact(fp, NULL, &fact) == 1){
		VAR.PREDICATE = Flights;
		VAR.VAR_1 = fact.values[0];
		VAR.VAR_2 = fact.values[1];
		VAR.VAR_3 = fact.values[2];
		VAR.VAR_4 = fact.values[3];
		VAR.VAR_5 = fact.values[4];

#ifdef NDEBUG
		fprintf(stderr, "Adding rewriting variable: X_Flights(%i,%i,%i,%i,%i)\n",
				VAR.VAR_1,
				VAR.VAR_2,
				VAR.VAR_3,
				VAR.VAR_4,
				VAR.VAR_5);
#endif

		SolverQueue_append(&solver, &VAR);
	}
	fclose(fp);

	fp_Reaches = fopen(tuples_output_files[0], "w+");

	return TRUE;
}

int solver_compute(){
	intList *t1;
	SolverNode current;
	TYPE_REWRITING_VARIABLE VAR;

	while (solver.head){
		current = solver.head;

		if (current->b.PREDICATE == Flights){
#ifdef NDEBUG
			fprintf(stderr, "Handling rewriting variable: X_Flights(%i, %i, %i, %i, %i)\n",
					current->b.VAR_1,
					current->b.VAR_2,
					current->b.VAR_3,
					current->b.VAR_4,
					current->b.VAR_5);
#endif
			VAR.PREDICATE = Reaches;
			VAR.VAR_1 = current->b.VAR_2;
			VAR.VAR_2 = current->b.VAR_3;

			if (!Ds_contains_solution_Reaches(VAR.VAR_1, VAR.VAR_2)){
#ifdef NDEBUG
				fprintf(stderr, "\tAdding variable -> ");
				print_rewriting_variable(stderr, &VAR);
				fprintf(stderr, "\n");
#endif

				SolverQueue_append(&solver, &VAR);
				Ds_append_solution_Reaches(VAR.VAR_1, VAR.VAR_2);
			}
		}

		if (current->b.PREDICATE == Reaches){
			print_answer(fp_Reaches, &current->b);
#ifdef NDEBUG
			fprintf(stderr, "Handling rewriting variable: X_Reaches(%i, %i)\n",
					current->b.VAR_1,
					current->b.VAR_2);
#endif
			t1 = Ds_get_intList_1(Reaches_view_1, current->b.VAR_2);
			for (; t1; t1 = t1->next){
				VAR.PREDICATE = Reaches;
				VAR.VAR_1 = current->b.VAR_1;
				VAR.VAR_2 = t1->value;

				if (!Ds_contains_solution_Reaches(VAR.VAR_1, VAR.VAR_2)){
#ifdef NDEBUG
					fprintf(stderr, "\tAdding variable -> ");
					print_rewriting_variable(stderr, &VAR);
					fprintf(stderr, "\n");
#endif

					SolverQueue_append(&solver, &VAR);
					Ds_append_solution_Reaches(VAR.VAR_1, VAR.VAR_2);
				}
			}

			t1 = Ds_get_intList_1(Reaches_view_2, current->b.VAR_1);
			for (; t1; t1 = t1->next){
				VAR.PREDICATE = Reaches;
				VAR.VAR_1 = t1->value;
				VAR.VAR_2 = current->b.VAR_2;

				if (!Ds_contains_solution_Reaches(VAR.VAR_1, VAR.VAR_2)){
#ifdef NDEBUG
					fprintf(stderr, "\tAdding variable -> ");
					print_rewriting_variable(stderr, &VAR);
					fprintf(stderr, "\n");
#endif

					SolverQueue_append(&solver, &VAR);
					Ds_append_solution_Reaches(VAR.VAR_1, VAR.VAR_2);
				}
			}


#ifdef NDEBUG
		fprintf(stderr, "\tData structure: Adding Reaches_view_1(%i, %i)\n", current->b.VAR_1, current->b.VAR_2);
		fprintf(stderr, "\tData structure: Adding Reaches_view_2(%i, %i)\n", current->b.VAR_2, current->b.VAR_1);
#endif
			Ds_insert_2(Reaches_view_1, current->b.VAR_1, current->b.VAR_2);
			Ds_insert_2(Reaches_view_2, current->b.VAR_2, current->b.VAR_1);
		}

		solver.head = solver.head->next;
		free(current);
	}

	return TRUE;
}

void solver_free(){
	fclose(fp_Reaches);

	Ds_free();
	SolverQueue_free(&solver);
	Mem_free();
}
