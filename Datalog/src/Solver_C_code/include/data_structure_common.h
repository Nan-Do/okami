/*
 * data_structure_common.h
 *
 * Created by: C Code Generator
 * Created on: 2014-01-21
 */
 
#ifndef DATA_STRUCTURE_COMMON_H_
#define DATA_STRUCTURE_COMMON_H_

struct intList{
	unsigned int value;
	struct intList *next;
};
typedef struct intList intList;

extern void intList_free(intList *);
extern void intList_append(intList **, int);

#endif
