%% fill_Header

#include <memory>
#include <mutex>
#include <set>

#include "libcuckoo/cuckoohash_map.hh"

#include "lockedvectorint.hh"
#include "lockedbitset.hh"
#include "views.hh"

#ifndef DATASTRUCTURE_H_
#define DATASTRUCTURE_H_

class Datastructure {

private:
%% fillDatastructureCreateNodeStructs

%% fillDatastructureRootData

public:
    Datastructure() {}

%% fillDatastructureHeaders
};

#endif
