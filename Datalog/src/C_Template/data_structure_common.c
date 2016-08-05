%% fill_Header

#include <stdlib.h>

#include "data_structure_common.h"

void uIntList_init(uIntList *l){
    l->head = NULL;
}

void uIntList_free(uIntList *l){
    uIntNodePtr temp;
    for (temp = l->head; temp; l->head = l->head->next, temp = l->head)
        free(temp);
}

void uIntList_append(uIntList *l, int value){
    uIntNodePtr e;
    
    e = malloc(sizeof(uIntNode));
    e->value = value;
    e->next = l->head;
    l->head = e;
}
