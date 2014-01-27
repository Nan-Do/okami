Information of the compiler prototype.

Directories
src/
- This directory includes the source code for the compiler
examples/
- Some datalog examples to be used with the compiler
tests/
- tests cases for the compiler

The compiler is still in an alpha status many bugs and missbehaviors are
expected.
To use it python 2.7 is required. To compile the c generated code aside
from the make tool and gcc the judy array is required (http://judy.sourceforge.net/)

In ubuntu it can be installed with:
	sudo apt-get install libjudydebian1 libjudy-dev

The different options of the compiler are explained in the help.
In order to work the compiler expects the directory C_Template to exist
in the same directory as the main.py (and the rest of py files).
The compiler will generate an output directory called Solver_C_code. The location
of this directory can be controlled by the input parameters.
The generated solver will expect several input file called as the different extensional predicates of the datalog program.
For example if there is an extensional predicate A in the datalog program:
The solver expects a file called A.tuples in the same directory.
The input format must be (it only accepts integer as arguments):
A(1,0).
A(2,0).
...
A(9,9).

For example for Andersen's pointer analysis:
-Generate the source code for the solver (starting at src dir):
   python main.py -p vP ../examples/pointerAnalysis.dl

-Compile the solver:
   cd Solver_C_code
   make

-Create the next files (in the same directory as the solver binary):
   Name:
    A.tuples
   Contents:
    A(2, 1).

   Name:
    L.tuples
   Contents:
    L(1, 0, 3).

   Name: 
    S.tuples
   Contents:
    S(1, 0, 2).

   Name:
    vP0.tuples
   Contents:
    vP0(1, 0).
    vP0(2, 1).

-Execute the solver
   ./solver

The output at stdout should be:
   vP(1, 0).
   vP(2, 1).
   vP(2, 0).
   vP(3, 0).
   vP(3, 1).

There is a debug mode which can be specified in the make file which will
output information of the flow of the rewriting variables.
