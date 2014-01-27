/*
 * data_structure.h
 *
 * Created by: C Code Generator
 * Created on: 2014-01-21
 */

#ifndef DATA_STRUCTURE_H_
#define DATA_STRUCTURE_H_

#include "utils.h"
#include "data_structure_common.h"

extern void Ds_init();
extern void Ds_free();

extern void Ds_insert_2(int, int, int);

extern int  Ds_contains_solution_Reaches(int, int);
extern void Ds_append_solution_Reaches(int, int);

extern intList * Ds_get_intList_1(int, int);

#endif /* DATA_STRUCTURE_H_ */
