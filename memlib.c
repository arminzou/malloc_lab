/*
 * memlib.c - a module that simulates the memory system.  Needed
 * because it allows us to interleave calls from the student's malloc
 * package with the system's malloc package in libc.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>

#include "memlib.h"
#include "config.h"

/* private global variables */
static unsigned char *heap;                 /* Starting address of heap */
static unsigned char *mem_brk;              /* Current position of break */
static unsigned char *mem_max_addr;         /* Maximum allowable heap address */
static size_t mmap_length;                  /* Number of bytes allocated by mmap */

/* 
 * mem_init - initialize the memory system model
 */
void mem_init(){
    /* Dense allocation */
    mmap_length = MAX_DENSE_HEAP;

    int dev_zero = open("/dev/zero", O_RDWR);
    void *start = TRY_DENSE_HEAP_START;
    void *addr = mmap(start,        /* suggested start*/
		      mmap_length,  /* length */
		      PROT_WRITE,   /* permissions */
		      MAP_PRIVATE,  /* private or shared? */
		      dev_zero,	    /* fd */
		      0);	    /* offset */
    if (addr == MAP_FAILED) {
	fprintf(stderr, "FAILURE.  mmap couldn't allocate space for heap\n");
	exit(1);
    }
    heap = addr;
    mem_max_addr = heap + MAX_DENSE_HEAP;
    mem_reset_brk();
}

/* 
 * mem_deinit - free the storage used by the memory system model
 */
void mem_deinit(void){
    munmap(heap, mmap_length);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
 */
void mem_reset_brk(){
    mem_brk = heap;
}

/* 
 * mem_sbrk - simple model of the sbrk function. Extends the heap 
 *		by incr bytes and returns the start address of the new area. In
 *		this model, the heap cannot be shrunk.
 */
void *mem_sbrk(intptr_t incr) {
    unsigned char *old_brk = mem_brk;

    bool ok = true;
    if (incr < 0) {
	ok = false;
	fprintf(stderr, "ERROR: mem_sbrk failed.  Attempt to expand heap by negative value %ld\n", (long) incr);
    } else if (mem_brk + incr > mem_max_addr) {
	ok = false;
	size_t alloc = mem_brk - heap + incr;
	fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory.  Would require heap size of %zd (0x%zx) bytes\n", alloc, alloc);
    }
    if (ok) {
	mem_brk += incr;
	return (void *) old_brk;
    } else {
	errno = ENOMEM;
	return (void *) -1;
    }
}

/*
 * mem_heap_lo - return address of the first heap byte
 */
void *mem_heap_lo(){
    return (void *) heap;
}

/* 
 * mem_heap_hi - return address of last heap byte
 */
void *mem_heap_hi(){
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
 */
size_t mem_heapsize() {
    return (size_t)(mem_brk - heap);
}

/*
 * mem_pagesize() - returns the page size of the system
 */
size_t mem_pagesize(){
    return (size_t) getpagesize();
}

/*************** Memory emulation  *******************/

/* Read len bytes and return value zero-extended to 64 bits */
uint64_t mem_read(const void *addr, size_t len) {
    uint64_t rdata;
    /* Dense or non-heap read */
    rdata = *(uint64_t *) addr;
    if (len < sizeof(uint64_t)) {
	uint64_t mask = ((uint64_t) 1 << (8 * len)) - 1;
	rdata &= mask;
    }
    return rdata;
}

/* Write lower order len bytes of val to address */
void mem_write(void *addr, uint64_t val, size_t len) {
    /* Dense or non-heap write */
    if (len == sizeof(uint64_t))
        *(uint64_t *) addr = val;
    else
        memcpy(addr, (void *) &val, len);
}

/* Emulation of memcpy */
void *mem_memcpy(void *dst, const void *src, size_t n) {
    void *savedst = dst;
    size_t w = sizeof(uint64_t);
    while (n >= w) {
	uint64_t data = mem_read(src, w);
	mem_write(dst, data, w);
	n -= w;
	src = (void *) ((unsigned char *) src + w);
	dst = (void *) ((unsigned char *) dst + w);
    }
    if (n) {
	uint64_t data = mem_read(src, n);
	mem_write(dst, data, n);
    }
    return savedst;
}

/* Emulation of memset */
void *mem_memset(void *dst, int c, size_t n) {
    void *savedst = dst;
    uint64_t byte = c & 0xFF;
    uint64_t data = 0;
    size_t w = sizeof(uint64_t);
    size_t i;
    for (i = 0; i < w; i++) {
	data = data | (byte << (8*i));
    }
    while (n >= w) {
	mem_write(dst, data, w);
	n -= w;
	dst = (void *) ((unsigned char *) dst + w);
    }
    if (n) {
	mem_write(dst, data, n);	
    }
    return savedst;
}

/* Function to aid in viewing contents of heap */
void hprobe(void *ptr, int offset, size_t count) {
    unsigned char *cptr = (unsigned char *) ptr;
    unsigned char *cptr_lo = cptr+offset;
    unsigned char *cptr_hi = cptr_lo + count - 1;
    unsigned char *iptr;
    if ((void *) cptr_lo < mem_heap_lo()) {
	fprintf(stderr, "Invalid probe.  Address %p is below start of heap\n",
		cptr_lo);
	return;
    }
    if ((void *) cptr_hi > mem_heap_hi()) {
	fprintf(stderr, "Invalid probe.  Address %p is beyond end of heap\n",
		cptr_lo);
	return;
    }
    printf("Bytes %p...%p: 0x", cptr_hi, cptr_lo);
    for (iptr = cptr_hi; iptr >= cptr_lo; iptr--)
	printf("%.2x", (unsigned) mem_read((void *) iptr, 1));
    printf("\n");
}
