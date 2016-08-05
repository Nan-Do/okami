%% fill_Header
 
#ifndef DATA_STRUCTURE_COMMON_H_
#define DATA_STRUCTURE_COMMON_H_

struct uIntNode{
    unsigned int value;
    struct uIntNode *next;
};
typedef struct uIntNode uIntNode;
typedef struct uIntNode* uIntNodePtr;

struct uIntList{
    uIntNodePtr head;
};
typedef struct uIntList uIntList;

extern void uIntList_init(uIntList *);
extern void uIntList_free(uIntList *);
extern void uIntList_append(uIntList *, int);

#endif
