#FLAGS = -ggdb -Wall -O0 -static -DNDEBUG -Wextra -pedantic -ansi
FLAGS = -Wall -O3 -static -Wextra -ansi -fomit-frame-pointer -march=native -pipe
ARCH  = iX86
INCL  = -Iinclude 
LIB   = -lm -lJudy

all: solver

solver: main.c arena.o mem.o parser.o data_structure_common.o data_structure.o solver.o 
	$(CC) $(FLAGS) -o solver $(INCL) main.c arena.o mem.o data_structure_common.o data_structure.o parser.o solver.o $(LIB)

arena.o: arena.c include/arena.h
	$(CC) $(FLAGS) $(INCL) -c arena.c

mem.o: mem.c include/mem.h include/arena.h
	$(CC) $(FLAGS) $(INCL) -c mem.c
	
parser.o: parser.c include/parser.h
	$(CC) $(FLAGS) $(INCL) -c parser.c
	
data_structure_common.o: data_structure_common.c include/data_structure_common.h
	$(CC) $(FLAGS) $(INCL) -c data_structure_common.c

data_structure.o: data_structure.c include/data_structure.h include/data_structure_common.h
	$(CC) $(FLAGS) $(INCL) -c data_structure.c

solver.o: solver.c include/solver.h
	$(CC) $(FLAGS) $(INCL) -c solver.c

clean:
	rm -rf *.o datalogsolve

