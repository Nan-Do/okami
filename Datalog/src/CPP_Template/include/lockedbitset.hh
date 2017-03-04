%% fill_Header

#include <cstdlib>
#include <cstring>
#include <mutex>

#ifndef LOCKEDBITSET_H_
#define LOCKEDBITSET_H_

class LockedBitSet {

/* BitMap constants */
#define INITIAL_BITARRAY_SIZE 1000
#define BITMAP_BASE 32

private:
    struct BitMap {
        unsigned int size;
        unsigned int * bitarray;
    };
    typedef struct BitMap* BitMapPtr;

    BitMap bitmap;
    std::mutex bitset_lock;

    /* Bitmap functions */
    void BitMap_init(BitMapPtr b) {
        b->bitarray = (unsigned int *) std::malloc(sizeof(unsigned int) * INITIAL_BITARRAY_SIZE);
        std::memset(b->bitarray, 0, sizeof(unsigned int) * INITIAL_BITARRAY_SIZE);
        b->size = INITIAL_BITARRAY_SIZE;
    }

    void BitMap_free(BitMapPtr b) {
        std::free(b->bitarray);
        b->size = 0;
    }

    void BitMap_setBit(BitMapPtr b, unsigned int k) {
        int i, new_size;

        /* Check if we have to resize the bit array */
        if (k > (b->size * BITMAP_BASE)){
            new_size = (k / BITMAP_BASE) + 1;
            b->bitarray = (unsigned int *) std::realloc(b->bitarray, sizeof(int) * new_size);

            /* initialize the rest of the bitmap */
            for (i = b->size; i < new_size; i++)
                b->bitarray[i] = 0;
            b->size = new_size;
        }

        b->bitarray[k/BITMAP_BASE] |= (unsigned int) 1 << (k%BITMAP_BASE);
    }

    bool BitMap_testBit(BitMapPtr b, unsigned int k) {
        /* If the bitmap can't hold that value just ignore it */
        if (k > (b->size * BITMAP_BASE)) return false;

        return ((b->bitarray[k/BITMAP_BASE] & ((unsigned int) 1 << (k%BITMAP_BASE))) != 0);
    }

    void BitMap_clearBit(BitMapPtr b, unsigned int k) {
        /* If the bitmap can't hold that value just ignore it */
        if (k > (b->size * BITMAP_BASE)) return;

        b->bitarray[k/BITMAP_BASE] &= ~((unsigned int) 1 << (k%BITMAP_BASE));
    }

public:
    LockedBitSet() {
    	BitMap_init(&bitmap);
    }

    ~LockedBitSet() {
    	BitMap_free(&bitmap);
    }

    void lock() { bitset_lock.lock(); }
    void unlock() { bitset_lock.unlock(); }
    bool test(int x) { return BitMap_testBit(&bitmap, x); }
    void set(int x) { BitMap_setBit(&bitmap, x); }
};

#endif
