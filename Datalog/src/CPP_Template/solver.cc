%% fill_Header

#include <fstream>
#include <iostream>
#include <thread>
#include <sstream>
#include <string>
#include <vector>

#include "solver.hh"

/*
 * These two functions are used to parse the facts in
 * the init stratum functions.
 */
template<typename Out>
void split(const std::string &s, char delim, Out result) {
    std::stringstream ss;
    ss.str(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
        *(result++) = item;
    }
}

std::vector<std::string> split(const std::string &s, char delim) {
    std::vector<std::string> elems;
    split(s, delim, std::back_inserter(elems));
    return elems;
}

%% fillSolverWriteRewritingVariable

%% fillSolverInitFunction

%% fillSolverInitStratumFunctions

%% fillSolverComputeStratumClasses

%% fillSolverComputeFunction

%% fillSolverEndFunction
