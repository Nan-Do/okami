%% fill_Header

#ifndef ARENA_INCLUDED
#define ARENA_INCLUDED

#define T Arena_T
typedef struct T *T;

extern T    Arena_new    (void);
extern void Arena_dispose(T *ap);
extern void *Arena_alloc (T arena, long nbytes,
	const char *file, int line);
extern void  Arena_free  (T arena);
#undef T
#endif
