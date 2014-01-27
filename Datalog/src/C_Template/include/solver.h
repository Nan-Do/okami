%% fill_Header

#ifndef SOLVER_H_
#define SOLVER_H_

struct STRUCT_REWRITING_VARIABLE {
%% fill_RewritingVariable
};
typedef struct STRUCT_REWRITING_VARIABLE TYPE_REWRITING_VARIABLE;

extern int solver_init();
extern int solver_compute();
extern void solver_free();
extern void solver_print_solution(FILE *);

#endif
