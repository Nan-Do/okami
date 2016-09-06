#FLAGS = -ggdb -Wall -O0 -static -DNDEBUG -Wextra -pedantic -ansi -std=c99
FLAGS = -Wall -O3 -static -Wextra -ansi -fomit-frame-pointer -march=native -pipe -std=c99
ARCH  = iX86
INCL  = -Iinclude 
%% fill_MakefileLibs

all: solver

solver: main.c parser.o data_structure_common.o data_structure.o solver.o solver_queue.o 
	$(CC) $(FLAGS) -o solver $(INCL) main.c data_structure_common.o data_structure.o parser.o solver.o solver_queue.o $(LIB)

parser.o: parser.c include/parser.h
	$(CC) $(FLAGS) $(INCL) -c parser.c
	
data_structure_common.o: data_structure_common.c include/data_structure_common.h
	$(CC) $(FLAGS) $(INCL) -c data_structure_common.c

data_structure.o: data_structure.c include/data_structure.h include/data_structure_common.h
	$(CC) $(FLAGS) $(INCL) -c data_structure.c

solver.o: solver.c include/solver.h
	$(CC) $(FLAGS) $(INCL) -c solver.c
	
solver_queue.o: solver_queue.c include/solver_queue.h
	$(CC) $(FLAGS) $(INCL) -c solver_queue.c

clean:
	rm -rf *.o datalogsolve

