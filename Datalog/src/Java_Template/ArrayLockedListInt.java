%% fill_Header

import java.util.ArrayList;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class ArrayLockedListInt {
	private ArrayList<Integer> array;
	private Lock lock;
	
	ArrayLockedListInt(){
		array = new ArrayList<Integer>();
		lock = new ReentrantLock();
	}
	
	void lock() { lock.lock(); }
	void unlock() { lock.unlock(); }
	void add(int x) { array.add(x); }
	ArrayList<Integer> get_array() { return array; }
}
