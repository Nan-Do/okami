%% fill_Header

#include <vector>
#include <mutex>

#ifndef LOCKEDVECTORINT_H_
#define LOCKEDVECTORINT_H_

class LockedVectorInt {
private:
	std::vector<int> array;
	std::mutex array_lock;

public:
	void lock() { array_lock.lock(); }
	void unlock() { array_lock.unlock(); }
	void add(int x_1) { array.push_back(x_1); }
	std::vector<int> * get_array() {return &array; }
};

#endif
