#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "arena.h"
#define T Arena_T

#define THRESHOLD 10
struct T {
    T prev;
    char *avail;
    char *limit;
};
union align {
#ifdef MAXALIGN
    char pad[MAXALIGN];
#else
    int i;
    long l;
    long *lp;
    void *p;
    void (*fp)(void);
    float f;
    double d;
    long double ld;
#endif
};
union header {
    struct T b;
    union align a;
};
static T freechunks;
static int nfree;

T Arena_new(void) {
    T arena = malloc(sizeof (*arena));
    if (arena == NULL){
        printf("Error: Creating arena\n");
        abort();
    }
    arena->prev = NULL;
    arena->limit = arena->avail = NULL;
    return arena;
}

void Arena_dispose(T *ap) {
    /*assert(ap && *ap);*/
    Arena_free(*ap);
    free(*ap);
    *ap = NULL;
}

void *Arena_alloc(T arena, long nbytes, const char *file, int line) {
    /*assert(arena);
    assert(nbytes > 0);*/
    nbytes = ((nbytes + sizeof (union align) - 1)/
                (sizeof (union align)))*(sizeof (union align));
    while (nbytes > arena->limit - arena->avail) {
        T ptr;
        char *limit;
        if ((ptr = freechunks) != NULL) {
            freechunks = freechunks->prev;
            nfree--;
            limit = ptr->limit;
        } else {
            long m = sizeof (union header) + nbytes + 10*1024;
            ptr = malloc(m);
            if (ptr == NULL) {
                printf("Error: Allocating memory from the arena (%s:%i)\n", file, line);
                abort();
            }
            limit = (char *)ptr + m;
        }
	*ptr = *arena;
        arena->avail = (char *)((union header *)ptr + 1);
        arena->limit = limit;
        arena->prev  = ptr;
    }
    arena->avail += nbytes;
    return arena->avail - nbytes;
}

void Arena_free(T arena) {
    /*assert(arena);*/
    while (arena->prev) {
        struct T tmp = *arena->prev;
        if (nfree < THRESHOLD) {
            arena->prev->prev = freechunks;
            freechunks = arena->prev;
            nfree++;
            freechunks->limit = arena->limit;
        } else
            free(arena->prev);
            *arena = tmp;
        }
 
    assert(arena->limit == NULL);
    assert(arena->avail == NULL);
}
