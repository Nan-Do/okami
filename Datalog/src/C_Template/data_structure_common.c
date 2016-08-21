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

