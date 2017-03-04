%% fill_Header

import java.util.BitSet;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class LockBitSet {
	public BitSet bitset;
	public Lock lock;
	
	LockBitSet(){
		bitset = new BitSet();
		lock = new ReentrantLock();
	}
	
	void lock() { lock.lock(); }
    void unlock() { lock.unlock(); }
    boolean get(int x) { return bitset.get(x); }
    void set(int x) { bitset.set(x); }
	
	BitSet getBitSet() { return bitset; }
}
