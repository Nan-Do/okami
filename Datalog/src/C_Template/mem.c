%% fill_Header

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include "utils.h"
#include "mem.h"

Arena_T pool;

void Mem_init(){
    pool = Arena_new();
}

void Mem_free(){
    Arena_free(pool);
}

void *Mem_arena_alloc(long nbytes, const char *file, int line) {
    return Arena_alloc(pool, nbytes, file, line);
}

void *Mem_alloc(long nbytes, const char *file, int line) {
    void *ptr;
    ptr = malloc(nbytes);
    if (ptr == NULL) {
        if (file)
            fprintf(stderr, "%s: Error allocating memory %s:%i\n", PROGRAM_NAME, file, line);
        abort();
    }
    return ptr;
}

void *Mem_calloc(long count, long nbytes,
    const char *file, int line) {
    void *ptr;
    ptr = calloc(count, nbytes);
    if (ptr == NULL) {
        if (file)
            fprintf(stderr, "%s: Error allocating memory %s:%i\n", PROGRAM_NAME, file, line);
        abort();
        }
    return ptr;
}

void *Mem_resize(void *ptr, long nbytes, const char *file, int line){
    ptr = realloc(ptr, nbytes);
    if (ptr == NULL){
        if (file)
            fprintf(stderr, "%s: Error allocating memory %s:%i\n", PROGRAM_NAME, file, line);
        abort();
    }
    return ptr;
}

