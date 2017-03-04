%% fill_Header

#include <iostream>
#include <string>

#include "solver.hh"

int main(int argc, char *argv[]) {
    int num_threads = 1;
    Solver solver;

    if (argc == 2)
        num_threads = std::stoi(argv[1]);

    solver.init(num_threads);
    solver.compute();
    solver.end();

    return 0;
}
