%% fill_Header
 
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
    int * bitarray;
};
typedef struct BitMap BitMap;
typedef struct BitMap* BitMapPtr;

extern void BitMap_init(BitMapPtr);
extern void BitMap_free(BitMapPtr);
extern void BitMap_setBit(BitMapPtr, unsigned int);
extern int BitMap_testBit(BitMapPtr, unsigned int);
extern void BitMap_clearBit(BitMapPtr, unsigned int);
#endif
