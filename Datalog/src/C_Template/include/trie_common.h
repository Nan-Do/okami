%% fill_Header
 
#ifndef TRIE_COMMON_H_
#define TRIE_COMMON_H_

struct intList{
	unsigned int value;
	struct intList *next;
};
typedef struct intList intList;

extern void intList_free(intList *);
extern void intList_append(intList **, int);

#endif
