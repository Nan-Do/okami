%% fill_Header

#include <fstream>
#include <list>

#include "rewritingvariable.hh"
#include "datastructure.hh"

#ifndef SOLVER_H_
#define SOLVER_H_

class Solver {

private:
%% fillSolverPrivateDataAndFunctions
public:
    Solver() {}

    bool init(int);
    bool compute();
    bool end();
};

#endif
