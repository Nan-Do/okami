#FLAGS = -ggdb -Wall -O0 -DNDEBUG -Wextra -pedantic -ansi -std=c++11
FLAGS = -Wall -Ofast -Wextra -ansi -fomit-frame-pointer -flto -march=native -pipe -std=c++11
ARCH  = iX86
INCL  = -Iinclude 
LIB = -lpthread

all: solver

solver: main.cc datastructure.o solver.o 
	$(CXX) $(FLAGS) -o solver $(INCL) main.cc datastructure.o solver.o $(LIB)

datastructure.o: datastructure.cc include/datastructure.hh
	$(CXX) $(FLAGS) $(INCL) -c datastructure.cc

solver.o: solver.cc include/solver.hh
	$(CXX) $(FLAGS) $(INCL) -c solver.cc
	
clean:
	rm -rf *.o solver

