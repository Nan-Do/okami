%% fill_Header

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <unistd.h>

#include "utils.h"
#include "solver.h"

/*
 *	Main Function.
 */
 
int main(){
    if (!solver_init()){
        fprintf(stderr, "%s: Error building the rewriting system\n", PROGRAM_NAME);
        exit(1);
    }

    if (!solver_compute()){
        fprintf(stderr, "%s: Error solving the rewriting system\n", PROGRAM_NAME);
        exit(1);
    }

    solver_free();

    return EXIT_SUCCESS;
}
