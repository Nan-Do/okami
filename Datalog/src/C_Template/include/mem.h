%% fill_Header

#ifndef MEM_H
#define MEM_H

#include <stdlib.h>
#include "arena.h"

extern void Mem_init();
extern void Mem_free();

extern void *Mem_alloc (long nbytes,
                        const char *file, int line);
	
extern void *Mem_calloc(long count, long nbytes,
                        const char *file, int line);
	
extern void *Mem_resize(void *ptr, long nbytes,
                        const char *file, int line);
	
extern void *Mem_arena_alloc(long nbytes, const char *file, int line);

#define ALLOC(nbytes) \
        Mem_alloc((nbytes), __FILE__, __LINE__)
#define CALLOC(count, nbytes) \
        Mem_calloc((count), (nbytes), __FILE__, __LINE__)
#define RESIZE(ptr, nbytes) ((ptr) = Mem_resize((ptr), \
        (nbytes), __FILE__, __LINE__))
#define NEW(p) ((p) = ALLOC((long)sizeof *(p)))
#define FREE(ptr) ((void) (free((ptr))))

#define ARENA_ALLOC(ptr) \
        ((ptr) = Mem_arena_alloc((long)sizeof * (ptr), __FILE__, __LINE__));

#endif
