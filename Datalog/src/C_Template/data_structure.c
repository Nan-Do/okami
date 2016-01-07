%% fill_Header

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <Judy.h>

#include "data_structure.h"
#include "mem.h"

/* Root level */
static Pvoid_t root;
%% fill_DsRootAnswers
/* This variable is made to scan the level 0 */
Word_t Index;
short first_value;

/* Nodes for the different levels of the data structure */
%% fill_DsLevelNodes

/* Datastructure control functions */
void Ds_init(){
    root = (Pvoid_t) NULL;
}

void Ds_free(){
    Word_t * PValue, index = 0;

    JLF(PValue, root, index);
    while (PValue != NULL){
%% fill_DsFreeLevel2Line

        JudyLDel(&root, index, PJE0);
        JLN(PValue, root, index);
    }
}

/* Functions to insert new values */
%% fill_DsInsertFunctions

/* Functions to get the different list of values */
void Ds_get_intValues_Level0_init(){
    Index = 0;
    first_value = 1;
}

short Ds_get_intValues_Level0(unsigned int *value){
    Word_t * PValue;

    if (first_value){
        first_value = 0;
        JLF(PValue, root, Index);
    }
    else{
        JLN(PValue, root, Index);
    }

    (*value) = Index;

    if (PValue){
        return 1;
    }

    return 0;
}

%% fill_DsGetIntListFunctions

/* Functions to check if a solution exists */
%% fill_DsContainSolutionFunctions

/* Functions to append solutions */
%% fill_DsAppendSolutionFunctions

/* Functions to create new nodes */
%% fill_DsLevelNewNodeFunctions

/* Functions to initialize the different levels */
%% fill_DsLevelInitLevelFunctions

/* Functions to free the different levels */
%% fill_DsLevelFreeFunctions
