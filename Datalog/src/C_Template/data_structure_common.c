%% fill_Header

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>

#include "data_structure_common.h"
#include "utils.h"

/* BitMap constants */
#define INITIAL_BITARRAY_SIZE 1000
#define BITMAP_BASE 32

/* Queue constants */
#define INITIAL_QUEUE_SIZE 16
#define QUEUE_SIZE_MODIFIER 2

/* Hash constants and macros */
#define HASH_INITIAL_SIZE 1024
#define HASH_FUNCTION integerHash_32

#define FIRST_CELL(hash) (h->m_cells + ((hash) & (h->m_arraySize - 1)))
#define CIRCULAR_NEXT(c) ((c) + 1 != h->m_cells + h->m_arraySize ? (c) + 1 : h->m_cells)
#define CIRCULAR_OFFSET(a, b) ((b) >= (a) ? (b) - (a) : h->m_arraySize + (b) - (a))

/* BTreeSet constants and definitions */
#define BTREE_SET_MAX_KEYS 1024

/* BTree constants and definitions */
#define BTREE_MAX_KEYS 1024

struct BTreeSetNode{
    bool isLeaf;                                      /* Is this node a leaf node?             */
    unsigned int numKeys;                                      /* How many keys does this node contain? */
    unsigned int keys[BTREE_SET_MAX_KEYS];            /* The actual keys                       */
    struct BTreeSetNode *kids[BTREE_SET_MAX_KEYS+1];  /* Kids[i] holds nodes < keys[i]         */
};



/*
  Next we have the implementations for the lists of the based stack 
  compositional data structure.
  
  The uIntArrayQueue and the uIntStack implementations are used to keep track
  of the successors of a path. Only one can be used. The compiler will use
  one of them as the user desires. The uIntArrayQueue is the default.
   
  The uIntArrayQueue is an array queue that grows as needed.
  The uIntStack is a linked list that grows from the head therefore acting as 
  a stack. 
*/

/* Queue Array implementation*/
void uIntArrayQueue_init(uIntArrayQueuePtr l){
    l->last = 0;
    l->max_size = INITIAL_QUEUE_SIZE;
    l->values = malloc(sizeof(unsigned int) * INITIAL_QUEUE_SIZE);
}

void uIntArrayQueue_free(uIntArrayQueuePtr l){
    l->last = 0;
    free(l->values);
}

void uIntArrayQueue_append(uIntArrayQueuePtr l, unsigned int value){
    /* Check if we have to resize the array */
    if (l->last == l->max_size){
        l->values = realloc(l->values, sizeof(unsigned int) * (l->max_size * QUEUE_SIZE_MODIFIER));
        l->max_size *= QUEUE_SIZE_MODIFIER;
    }
    l->values[l->last++] = value;
}


/* List implementation */
void uIntListStack_init(uIntListStackPtr l){
    l->head = NULL;
}

void uIntListStack_free(uIntListStackPtr l){
    uIntListStackNodePtr temp;
    for (temp = l->head; temp; l->head = l->head->next, temp = l->head)
        free(temp);
}

void uIntListStack_append(uIntListStackPtr l, int value){
    uIntListStackNodePtr new;
    
    new = malloc(sizeof(uIntListStackNode));
    new->value = value;
    new->next = l->head;
    l->head = new;
}


/*
  Next we have the implementations for the leaf sets of the based stack 
  compositional data structure.
  
  The AVLTree and the BitMap implementations are used to keep track
  of the elements on a set. Only one can be used. The compiler will use
  one of them as the user desires. The BitMap is the default.
  
  The AVLTree is a classical AVL Tree used as a set.
  The BitMaps is a bitmap array that will grow as needed.
*/

/* AVL implementation */
/*
 * This implementation is a modified version of the AVL Tree from
 * http://www.geeksforgeeks.org/avl-tree-set-1-insertion/
 */

/* An AVL tree node */
/* A utility function to get maximum of two integers */
int max(int a, int b);
 
/* A utility function to get height of the tree */
int height(AVLNode *N)
{
    if (N == NULL)
        return 0;
    return N->height;
}
 
/* A utility function to get maximum of two integers */
int max(int a, int b)
{
    return (a > b)? a : b;
}
 
/* Helper function that allocates a new node with the given key and
    NULL left and right pointers. */
AVLNode *newNode(unsigned int key)
{
    AVLNode* node = (AVLNode*) malloc(sizeof(AVLNode));
    node->key   = key;
    node->left   = NULL;
    node->right  = NULL;
    node->height = 1;  /* new node is initially added at leaf */
    return(node);
}
 
/* A utility function to right rotate subtree rooted with y
   See the diagram given above. */
AVLNode *rightRotate(AVLNode *y)
{
    AVLNode *x = y->left;
    AVLNode *T2 = x->right;
 
    /* Perform rotation */
    x->right = y;
    y->left = T2;
 
    /* Update heights */
    y->height = max(height(y->left), height(y->right))+1;
    x->height = max(height(x->left), height(x->right))+1;
 
    /* Return new root */
    return x;
}
 
/* A utility function to left rotate subtree rooted with x
   See the diagram given above. */
AVLNode *leftRotate(AVLNode *x)
{
    AVLNode *y = x->right;
    AVLNode *T2 = y->left;
 
    /* Perform rotation */
    y->left = x;
    x->right = T2;
 
    /* Update heights */
    x->height = max(height(x->left), height(x->right))+1;
    y->height = max(height(y->left), height(y->right))+1;
 
    /* Return new root */
    return y;
}
 
/* Get Balance factor of node N */
int getBalance(AVLNode *N)
{
    if (N == NULL)
        return 0;
    return height(N->left) - height(N->right);
}
 
AVLTree AVLTree_insert(AVLTree node, unsigned int key)
{
    int balance; 
    
    /* 1.  Perform the normal BST rotation */
    if (node == NULL)
        return(newNode(key));
 
    /* AVL is acting like a set we don't allow duplicates */
    if (key == node->key) return node;
    
    if (key < node->key)
        node->left  = AVLTree_insert(node->left, key);
    else
        node->right = AVLTree_insert(node->right, key);
 
    /* 2. Update height of this ancestor node */
    node->height = max(height(node->left), height(node->right)) + 1;
 
    /* 3. Get the balance factor of this ancestor node to check whether
       this node became unbalanced */
    balance = getBalance(node);
 
    /* If this node becomes unbalanced, then there are 4 cases */
 
    /* Left Left Case */
    if (balance > 1 && key < node->left->key)
        return rightRotate(node);
 
    /* Right Right Case */
    if (balance < -1 && key > node->right->key)
        return leftRotate(node);
 
    /* Left Right Case */
    if (balance > 1 && key > node->left->key)
    {
        node->left =  leftRotate(node->left);
        return rightRotate(node);
    }
 
    /* Right Left Case */
    if (balance < -1 && key < node->right->key)
    {
        node->right = rightRotate(node->right);
        return leftRotate(node);
    }
 
    /* return the (unchanged) node pointer */
    return node;
}

short AVLTree_contains(AVLTree node, unsigned int key)
{
    AVLTree temp = node;
    
    while (temp != NULL){
        if (temp->key == key) return true;
        else if (key < temp->key) temp = temp->left;
        else temp = temp->right;
    }
    
    return false;
}

void AVLTree_init(AVLTree *root)
{
    *root = NULL;
}

void AVLTree_free(AVLTree node)
{
    if (node != NULL){
        AVLTree_free(node->left);
        AVLTree_free(node->right);
        free(node);
    }
}

void AVLTree_size(AVLTree root, int * size)
{
    if(root != NULL)
    {
        *size += 1;
        AVLTree_size(root->left, size);
        AVLTree_size(root->right, size);
    }
}

void AVLTree_preOrder(AVLTree root)
{
    if(root != NULL)
    {
        printf("%d ", root->key);
        AVLTree_preOrder(root->left);
        AVLTree_preOrder(root->right);
    }
}


/* BitMap Array implementation */
void BitMap_init(BitMapPtr b){
    b->bitarray = malloc(sizeof(unsigned int) * INITIAL_BITARRAY_SIZE);
    memset(b->bitarray, 0, sizeof(unsigned int) * INITIAL_BITARRAY_SIZE);
    b->size = INITIAL_BITARRAY_SIZE;
}

void BitMap_setBit(BitMapPtr b, unsigned int k){
    int i, new_size;
    
    /* Check if we have to resize the bit array */
    if (k > (b->size * BITMAP_BASE)){
        new_size = (k / BITMAP_BASE) + 1;
        b->bitarray = realloc(b->bitarray, sizeof(int) * new_size);
        
        /* initialize the rest of the bitmap */
        for (i = b->size; i < new_size; i++)
            b->bitarray[i] = 0;
        b->size = new_size;
    }
    
    b->bitarray[k/BITMAP_BASE] |= (unsigned int) 1 << (k%BITMAP_BASE);
}

void BitMap_clearBit(BitMapPtr b, unsigned int k)
{
    /* If the bitmap can't hold that value just ignore it */
    if (k > (b->size * BITMAP_BASE)) return;
    
    b->bitarray[k/BITMAP_BASE] &= ~((unsigned int) 1 << (k%BITMAP_BASE));
}

int BitMap_testBit(BitMapPtr b, unsigned int k)
{
    /* If the bitmap can't hold that value just ignore it */
    if (k > (b->size * BITMAP_BASE)) return false;
    
    return ((b->bitarray[k/BITMAP_BASE] & ((unsigned int) 1 << (k%BITMAP_BASE))) != 0);
}

void BitMap_free(BitMapPtr b){
    free(b->bitarray);
    b->size = 0;
}


/* Hash Table implementation */
/* This implementation is a modified version of the Hash Table from
 * https://github.com/preshing/CompareIntegerMaps
 */

/* Hashing functions */
/* from code.google.com/p/smhasher/wiki/MurmurHash3 */
static inline uint32_t integerHash_32(uint32_t h)
{
	h ^= h >> 16;
	h *= 0x85ebca6b;
	h ^= h >> 13;
	h *= 0xc2b2ae35;
	h ^= h >> 16;
	return h;
}

/* from code.google.com/p/smhasher/wiki/MurmurHash3 */
static inline uint64_t integerHash_64(uint64_t k)
{
	k ^= k >> 33;
	k *= 0xff51afd7ed558ccd;
	k ^= k >> 33;
	k *= 0xc4ceb9fe1a85ec53;
	k ^= k >> 33;
	return k;
}

void HashTable_Init(HashTable *h){
    /* Initialize regular cells */
    h->m_arraySize = HASH_INITIAL_SIZE;
    h->m_cells = malloc(sizeof(Cell) * HASH_INITIAL_SIZE);
    memset(h->m_cells, 0, sizeof(Cell) * h->m_arraySize);
    h->m_population = 0;

    /* Initialize zero cell */
    h->m_zeroUsed = 0;
    h->m_zeroCell.key = 0;
    h->m_zeroCell.value = 0;
}

void Repopulate(HashTable *h, size_t desiredSize)
{
    Cell *c, *cell, *oldCells, *end;

    assert((desiredSize & (desiredSize - 1)) == 0);   /* Must be a power of 2 */
    assert(h->m_population * 4  <= desiredSize * 3);

    /* Get start/end pointers of old array */
    oldCells = h->m_cells;
    end = h->m_cells + h->m_arraySize;

    /* Allocate new array */
    h->m_arraySize = desiredSize;
    h->m_cells = malloc(sizeof(Cell) * h->m_arraySize);
    memset(h->m_cells, 0, sizeof(Cell) * h->m_arraySize);

    /* Iterate through old array */
    for (c = oldCells; c != end; c++)
    {
        if (c->key)
        {
            /* Insert this element into new array */
            for (cell = FIRST_CELL(HASH_FUNCTION(c->key));; cell = CIRCULAR_NEXT(cell))
            {
                if (!cell->key)
                {
                    /* Insert here */
                    *cell = *c;
                    break;
                }
            }
        }
    }

    /* Delete old array */
    free(oldCells);
}

Cell* HashTable_Lookup(HashTable *h, size_t key)
{
    Cell* cell;

    if (key)
    {
        /* Check regular cells */
        for (cell = FIRST_CELL(HASH_FUNCTION(key));; cell = CIRCULAR_NEXT(cell))
        {
            if (cell->key == key)
                return cell;
            if (!cell->key)
                return NULL;
        }
    }
    else
    {
        /* Check zero cell */
        if (h->m_zeroUsed)
            return &h->m_zeroCell;
        return NULL;
    }
}


Cell* HashTable_Insert(HashTable *h, size_t key){
    Cell* cell;

    if (key)
    {
        /* Check for regular cells */
        for (;;)
        {
            for (cell = FIRST_CELL(HASH_FUNCTION(key));; cell = CIRCULAR_NEXT(cell))
            {
                if (cell->key == key)
                    return cell;        /* Found */
                if (cell->key == 0)
                {
                    /* Insert here */
                    if ((h->m_population + 1) * 4 >= h->m_arraySize * 3)
                    {
                        /* Time to resize */
                        Repopulate(h, h->m_arraySize * 2);
                        break;
                    }
                    ++h->m_population;
                    cell->key = key;
                    return cell;
                }
            }
        }
    }
    else
    {
        /* Check zero cell */
        if (!h->m_zeroUsed)
        {
            /* Insert here */
            h->m_zeroUsed = true;
            if (++h->m_population * 4 >= h->m_arraySize * 3)
			{
				/* Even though we didn't use a regular slot, let's keep the sizing rules consistent */
                Repopulate(h, h->m_arraySize * 2);
			}
        }
        return &h->m_zeroCell;
    }
}


void HashTable_Free(HashTable *h){
    free(h->m_cells);
    h->m_arraySize = h->m_population = h->m_zeroUsed = 0;
}


/*
 * Implementation of the functions for the BTree as a set of integers
 * It is a modified version of the BTree found at
 * http://www.cs.yale.edu/homes/aspnes/pinewiki/BTrees.html
 */
/* Return smallest index i in sorted array such that key <= a[i] */
/* (or n if there is no such index) */
static unsigned int private_BTreeSet_SearchKey(int n, const unsigned int *a, unsigned int key){
    unsigned int lo, hi, mid;

    /* Invariant: a[lo] < key <= a[hi] */
    lo = -1;
    hi = n;

    while(lo + 1 < hi) {
        mid = (lo+hi)/2;
        if(a[mid] == key) {
            return mid;
        } else if(a[mid] < key) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    return hi;
}

/* Insert a new key into a tree */
/* returns new right sibling if the node splits */
/* and puts the median in *median */
/* else returns 0 */
static BTreeSet private_BTreeSet_Insert_Internal(BTreeSet b, unsigned int key, unsigned int *median){
    unsigned int pos, mid;
    BTreeSet b2;

    pos = private_BTreeSet_SearchKey(b->numKeys, b->keys, key);

    if(pos < b->numKeys && b->keys[pos] == key) {
        /* nothing to do */
        return NULL;
    }

    if(b->isLeaf) {

        /* everybody above pos moves up one space */
        memmove(&b->keys[pos+1], &b->keys[pos], sizeof(*(b->keys)) * (b->numKeys - pos));
        b->keys[pos] = key;
        b->numKeys++;

    } else {

        /* insert in child */
        b2 = private_BTreeSet_Insert_Internal(b->kids[pos], key, &mid);

        /* maybe insert a new key in b */
        if(b2) {

            /* every key above pos moves up one space */
            memmove(&b->keys[pos+1], &b->keys[pos], sizeof(*(b->keys)) * (b->numKeys - pos));
            /* new kid goes in pos + 1*/
            memmove(&b->kids[pos+2], &b->kids[pos+1], sizeof(*(b->keys)) * (b->numKeys - pos));

            b->keys[pos] = mid;
            b->kids[pos+1] = b2;
            b->numKeys++;
        }
    }

    /* we waste a tiny bit of space by splitting now
     * instead of on next insert */
    if(b->numKeys >= BTREE_SET_MAX_KEYS) {
        mid = b->numKeys/2;

        *median = b->keys[mid];

        /* make a new node for keys > median */
        /* picture is:
         *
         *      3 5 7
         *      A B C D
         *
         * becomes
         *          (5)
         *      3        7
         *      A B      C D
         */
        b2 = malloc(sizeof(*b2));

        b2->numKeys = b->numKeys - mid - 1;
        b2->isLeaf = b->isLeaf;

        memmove(b2->keys, &b->keys[mid+1], sizeof(*(b->keys)) * b2->numKeys);
        if(!b->isLeaf) {
            memmove(b2->kids, &b->kids[mid+1], sizeof(*(b->kids)) * (b2->numKeys + 1));
        }

        b->numKeys = mid;

        return b2;
    } else {
        return NULL;
    }
}

BTreeSet BTreeSet_Init(void){
    BTreeSet b;

    b = malloc(sizeof(*b));
    assert(b);

    b->isLeaf = true;
    b->numKeys = 0;

    return b;
}

void BTreeSet_Free(BTreeSet b){
    unsigned int i;

    if(!b->isLeaf) {
        for(i = 0; i < b->numKeys + 1; i++) {
            BTreeSet_Free(b->kids[i]);
        }
    }

    free(b);
}

bool BTreeSet_Contains(BTreeSet b, unsigned int key){
    unsigned int pos;

    /* have to check for empty tree */
    if(b->numKeys == 0) {
        return false;
    }

    /* look for smallest position that key fits below */
    pos = private_BTreeSet_SearchKey(b->numKeys, b->keys, key);

    if(pos < b->numKeys && b->keys[pos] == key) {
        return true;
    } else {
        return(!b->isLeaf && BTreeSet_Contains(b->kids[pos], key));
    }
}

void BTreeSet_Insert(BTreeSet b, unsigned int key){
    BTreeSet b1;   /* new left child */
    BTreeSet b2;   /* new right child */
    unsigned int median;

    b2 = private_BTreeSet_Insert_Internal(b, key, &median);

    if(b2) {
        /* basic issue here is that we are at the root */
        /* so if we split, we have to make a new root */

        b1 = malloc(sizeof(*b1));
        assert(b1);

        /* copy root to b1 */
        memmove(b1, b, sizeof(*b));

        /* make root point to b1 and b2 */
        b->numKeys = 1;
        b->isLeaf = false;
        b->keys[0] = median;
        b->kids[0] = b1;
        b->kids[1] = b2;
    }
}


/*
 * Implementation for the BTree functions.
 * As a difference with the previous one this BTree has been
 * designed with pointers working as an associative data structure
 * instead that with just integers.
 */

void private_BTree_Split(BTree x, int i, BTree y){
    int j, median = (BTREE_MAX_KEYS / 2);
    BTree z = BTree_Init();

    /* z and y are siblings */
    /* We copy the (t-1) superior elements of y */
    z->m_leaf = y->m_leaf;
    z->m_numkeys = median - 1;

    /* Update the z and y nodes */
    for (j = 0; j < median; j++) z->m_cells[j] = y->m_cells[j + median + 1];

    /* If it is not a leaf we also have to copy the pointers */
    if (!y->m_leaf)
        for (j = 0; j < (median + 1); j++) z->m_children[j] = y->m_children[j + median];

    /* Update the number of keys on y */
    y->m_numkeys = median;

    /* Move the pointers on x */
    for (j = (x->m_numkeys + 1); j > i; j--) x->m_children[j] = x->m_children[(j - 1)];
    x->m_children[(i + 1)] = z;

    /* Move keys on the parent */
    for (j = x->m_numkeys; j > i; j--) x->m_cells[j] = x->m_cells[(j - 1)];

    /* Move the central key up and update the counter */
    x->m_cells[i] = y->m_cells[median];
    x->m_numkeys++;
}

static int private_BTree_SearchLevelKey(const Cell *a, int n, unsigned int key){
	unsigned int lo, hi, mid;

    /* invariant: a[lo] < key <= a[hi] */
    lo = -1;
    hi = n;

    while(lo + 1 < hi){
        mid = (lo+hi)/2;

        if(a[mid].key == key)
            return mid;
        else if(a[mid].key < key)
            lo = mid;
        else
            hi = mid;
    }

    return hi;
}

static Cell * private_BTree_Insert_NonFull(BTree b, unsigned int key){
	unsigned int pos = private_BTree_SearchLevelKey(b->m_cells, b->m_numkeys, key);

    /* Check if the element is already on the Tree */
	/*
	 * The cells are initialized with a NULL value (0), if we ask for a zero key we might
	 * deduce that the key is in the array when it is really not. To be sure that the key is
	 * indeed in the array we have to make sure that the key of the cell is indeed set. To do
	 * that we have to check also that the value of the cell is not null.
	 */
    if (b->m_cells[pos].key == key && b->m_cells[pos].value){
        return NULL;
    }

    if (b->m_leaf){
        /* Everybody above pos moves up one space */
        memmove(&b->m_cells[pos+1], &b->m_cells[pos], sizeof(*(b->m_cells)) * (b->m_numkeys - pos));

        /* Update the tree and return the cell */
        b->m_numkeys++;
        b->m_cells[pos].key = key;
        return &b->m_cells[pos];
    }
    else{
        /* Do we need to split the node? */
        if(b->m_children[pos]->m_numkeys == BTREE_MAX_KEYS){
            private_BTree_Split(b, pos, b->m_children[pos]);
            if(key > b->m_cells[pos].key) pos++;
        }
        return private_BTree_Insert_NonFull(b->m_children[pos], key);
    }
}


BTree BTree_Init(){
    BTree b;

    b = malloc(sizeof(*b));
    assert(b);

    b->m_numkeys = 0;
    b->m_leaf = true;
    b->m_cells = malloc(sizeof(Cell) * BTREE_MAX_KEYS);
    b->m_children = malloc(sizeof(BTreeNode *) * (BTREE_MAX_KEYS+1));

    return b;
}

void BTree_Free(BTree b, void (*f)(size_t)){
	unsigned int i;

	/* Free the node values */
	for (i=0; i < b->m_numkeys; i++)
	    f(b->m_cells[i].value);

    if(!b->m_leaf)
        for(i = 0; i < b->m_numkeys + 1; i++)
            BTree_Free(b->m_children[i], f);

    free(b->m_cells);
    free(b->m_children);
    free(b);
}

Cell* BTree_Lookup(BTree b, unsigned int key){
	unsigned int pos;

    /* have to check for empty tree */
    if(b->m_numkeys == 0){
        return NULL;
    }

    /* look for smallest position that key fits below */
    pos = private_BTree_SearchLevelKey(b->m_cells, b->m_numkeys, key);

    if(pos < b->m_numkeys && b->m_cells[pos].key == key && b->m_cells[pos].value)
        return &b->m_cells[pos];
    else if (b->m_leaf)
        return NULL;
    else
        return BTree_Lookup(b->m_children[pos], key);
}

Cell* BTree_Insert(BTree *b, unsigned int key){
    BTree temp = *b, new_node;

    /* Is the node full? */
    if (temp->m_numkeys == BTREE_MAX_KEYS){
        new_node = BTree_Init();
        new_node->m_leaf = false;
        new_node->m_children[0] = temp;
        *b = new_node;
        private_BTree_Split(new_node, 0, temp);
        return private_BTree_Insert_NonFull(new_node, key);
    }
    else{
        return private_BTree_Insert_NonFull(temp, key);
    }
}

void BTree_Fill_KeysList(BTree b, BTreeKeyList **l){
    unsigned int i;
    BTreeKeyList *temp;

    if(!b->m_leaf)
        for(i = 0; i < b->m_numkeys + 1; i++)
        	BTree_Fill_KeysList(b->m_children[i], l);

    for (i=0; i < b->m_numkeys; i++){
		temp = malloc(sizeof(BTreeKeyList));
		temp->value = b->m_cells[i].key;
		temp->next = (*l);
		*l = temp;
	}
}
