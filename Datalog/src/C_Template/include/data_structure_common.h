%% fill_Header
 
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
