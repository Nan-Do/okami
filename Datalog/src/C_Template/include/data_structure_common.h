%% fill_Header
 
#include <stdlib.h>
#include <stdbool.h>

#ifndef DATA_STRUCTURE_COMMON_H_
#define DATA_STRUCTURE_COMMON_H_

/* Queue header functions */
struct uIntArrayQueue{
    long last, max_size;
    unsigned int *values;
};
typedef struct uIntArrayQueue uIntArrayQueue;
typedef struct uIntArrayQueue* uIntArrayQueuePtr;

extern void uIntArrayQueue_init(uIntArrayQueuePtr);
extern void uIntArrayQueue_free(uIntArrayQueuePtr);
extern void uIntArrayQueue_append(uIntArrayQueuePtr, unsigned int);


/* Stack header functions */
struct uIntListStackNode{
    unsigned int value;
    struct uIntListStackNode *next;
};
typedef struct uIntListStackNode uIntListStackNode;
typedef struct uIntListStackNode* uIntListStackNodePtr;

struct uIntListStack{
    uIntListStackNodePtr head;
};
typedef struct uIntListStack uIntListStack;
typedef struct uIntListStack* uIntListStackPtr;

extern void uIntListStack_init(uIntListStackPtr);
extern void uIntListStack_free(uIntListStackPtr);
extern void uIntListStack_append(uIntListStackPtr, int);


/* AVL header functions */
struct AVLNode
{
    unsigned int key;
    struct AVLNode *left;
    struct AVLNode *right;
    int height;
};
typedef struct AVLNode AVLNode;
typedef struct AVLNode* AVLTree;

extern void AVLTree_init(AVLTree *);
extern void AVLTree_free(AVLTree);
extern AVLTree AVLTree_insert(AVLTree, unsigned int);
extern short AVLTree_contains(AVLTree, unsigned int);
extern void AVLTree_preOrder(AVLTree root);
extern void AVLTree_size(AVLTree root, int *);

/* BitMap header functions */
struct BitMap{
    unsigned int size;
    unsigned int * bitarray;
};
typedef struct BitMap BitMap;
typedef struct BitMap* BitMapPtr;

extern void BitMap_init(BitMapPtr);
extern void BitMap_free(BitMapPtr);
extern void BitMap_setBit(BitMapPtr, unsigned int);
extern int BitMap_testBit(BitMapPtr, unsigned int);
extern void BitMap_clearBit(BitMapPtr, unsigned int);

/* Hash header functions */
/* Each member of the array */
struct Cell
{
        size_t key;
        size_t value;
};
typedef struct Cell Cell;

/* Hast Table definition */
struct HashTable
{
    Cell* m_cells;
    size_t m_arraySize;
    size_t m_population;
    bool m_zeroUsed;
    Cell m_zeroCell;
};
typedef struct HashTable HashTable;

/* Management functions */
extern void HashTable_Init(HashTable *);
extern void HashTable_Free(HashTable *);

/* Utilization functions */
extern Cell* HashTable_Insert(HashTable *, size_t);
extern Cell* HashTable_Lookup(HashTable *, size_t);

/* BTree as a Set for integers definition */
typedef struct BTreeSetNode BTreeSetNode;
typedef struct BTreeSetNode* BTreeSet;

/* Create a new empty tree */
BTreeSet BTreeSet_Init(void);

/* Free a tree */
void BTreeSet_Free(BTreeSet);

/* Insert a new element into a tree */
void BTreeSet_Insert(BTreeSet, unsigned int);

/* Return nonzero if key is present in tree */
bool BTreeSet_Contains(BTreeSet, unsigned int);

#endif
