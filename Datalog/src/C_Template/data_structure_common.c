%% fill_Header

#include <stdio.h>
#include <stdlib.h>

#include "data_structure_common.h"
#include "utils.h"

/* BitMap constants */
#define INITIAL_BITARRAY_SIZE 1000

#if __SIZEOF_POINTER__ == 8
#define BITMAP_BASE 64
#else
#define BITMAP_BASE 32
#endif

/* Queue constants */
#define INITIAL_QUEUE_SIZE 16
#define QUEUE_SIZE_MODIFIER 2


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
AVLNode *newNode(int key)
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
        if (temp->key == key) return TRUE;
        else if (temp->key > key) temp = temp->left;
        else temp = temp->right;
    }
    
    return FALSE;
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
    
    b->bitarray[k/BITMAP_BASE] |= 1 << (k%BITMAP_BASE);
}

void BitMap_clearBit(BitMapPtr b, unsigned int k)
{
    /* If the bitmap can't hold that value just ignore it */
    if (k > (b->size * BITMAP_BASE)) return;
    
    b->bitarray[k/BITMAP_BASE] &= ~(1 << (k%BITMAP_BASE));
}

int BitMap_testBit(BitMapPtr b, unsigned int k)
{
    /* If the bitmap can't hold that value just ignore it */
    if (k > (b->size * BITMAP_BASE)) return FALSE;
    
    return ((b->bitarray[k/BITMAP_BASE] & (1 << (k%BITMAP_BASE))) != 0);
}

void BitMap_free(BitMapPtr b){
    free(b->bitarray);
    b->size = 0;
}
