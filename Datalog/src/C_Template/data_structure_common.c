%% fill_Header

#include <stdlib.h>

#include "mem.h"
#include "data_structure_common.h"

void intList_free(intList *l){
	intList *temp;
	for (temp = l; temp; l = l->next, temp = l)
		free(temp);
}

void intList_append(intList **l, int value){
	intList *e;

	/*NEW(e);*/
	ARENA_ALLOC(e);

	e->value = value;	
	if (*l)
		e->next = *l;
	else
		e->next = NULL;

	(*l) = e;
}
