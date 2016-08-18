%% fill_Header

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

%% fill_DsFillJudyHeader

#include "data_structure.h"

/* Root level */
%% fill_DsRootLevel
%% fill_DsRootAnswers
/* This variable is made to scan the level 0 */
%% fill_DsScanZeroLevelVariables

/* Nodes for the different levels of the data structure */
%% fill_DsLevelNodes

/* Datastructure control functions */
void Ds_init(){
%% fill_DsInit
}

void Ds_free(){
%% fill_DsFree
}

/* Functions to insert new values */
%% fill_DsInsertFunctions

/* Functions to get the different list of values */
void Ds_get_intValues_Level0_init(){
%% fill_DsfillLevelZeroInit
}

short Ds_get_intValues_Level0(unsigned int *value){
%% fill_DsGetZeroValues
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
