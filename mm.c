/*
* mm.c
*
* The is a dynamic storage allocator that used best fit algorithem and segregated free list to 
* perform malloc, free and realloc function. Note that each free list has a unique size class.
*/


#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following. Be sure not
 * to have debugging enabled in your final submission
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16
#define HEADER_SIZE 8
#define FOOTER_SIZE 8
#define MIN_BLOCK_SIZE 32
#define EXTEND_SIZE 4096
#define SEG_LIST_SIZE 14

// size class of the segregated list
#define seg_size_class1 32
#define seg_size_class2 64
#define seg_size_class3 128
#define seg_size_class4 256
#define seg_size_class5 512
#define seg_size_class6 1024
#define seg_size_class7 2048
#define seg_size_class8 4096
#define seg_size_class9 8192
#define seg_size_class10 16384
#define seg_size_class11 32768
#define seg_size_class12 65536
#define seg_size_class13 131072

typedef void *blk_ptr;

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * Helper functions
 */
// compute the larger value given two values
static size_t max(size_t x, size_t y){ return ((x > y) ? (x) : (y));}
static size_t min(size_t x, size_t y){ return ((x < y) ? (x) : (y));}

// pack the size and the allocated bit into a word
static size_t pack(size_t size, int alloc){return ((size) | (alloc));}

// read and write at the address of bp
static size_t get(blk_ptr bp){return (*(size_t *)(bp));}
static void put(blk_ptr bp, size_t val){*((size_t *)(bp)) = val;}

// the address of bp points to ptr
static void putptr(blk_ptr bp, blk_ptr ptr){ *(size_t *)(bp) = (size_t)(ptr);}

// return the size of block given bp 
static size_t get_size(blk_ptr bp){return (size_t)(get(bp) & ~(0xf));}

// return the allocated bit given bp
static size_t get_alloc(blk_ptr bp){return (size_t)(get(bp) & 0x1);}

// compute the address of header and footer given bp
static size_t *p_to_header(void *bp){return ((size_t *)(bp) - 1);}
static size_t *p_to_footer(void *bp){return ((size_t *)((bp) + get_size(p_to_header(bp)) - 16));}

// compute the address of previous and next block given bp
static size_t *prev_bp(blk_ptr bp){return (size_t *)((bp) - get_size((bp) - 16));}
static size_t *next_bp(blk_ptr bp){return (size_t *)((bp) + get_size(p_to_header(bp)));}

// compute the address of previous and next free block given bp
static size_t *prev_freebp(blk_ptr bp){return ((size_t *)(bp));}
static size_t *next_freebp(blk_ptr bp){return ((size_t *)((bp) + 8));}

// compute the address of previous and next block in the list given bp
static size_t *prev_listbp(blk_ptr bp){return (*(size_t **)(bp));}
static size_t *next_listbp(blk_ptr bp){return (*(size_t **)(next_freebp(bp)));}

// declare segregated list array and heap pointer
blk_ptr seg_list[SEG_LIST_SIZE];
blk_ptr heap_list_ptr = NULL;

static blk_ptr extend_heap(size_t size);
static blk_ptr coalesce(void *ptr);
static blk_ptr place(void* ptr, size_t asize);
static void delete_list_blcok(void *ptr);
static void add_list_block(void *ptr, size_t size);
static int search_seg_list(size_t asize);
int mm_check(char *function);

// function that extends the heap and create free blocks
static blk_ptr extend_heap(size_t wsize){
	size_t asize = align(wsize);
	size_t *bp;
	
	if((size_t *)(bp = mem_sbrk(asize)) == (void *)-1){
		return NULL;
	}
	
	// add to segregated list
	add_list_block(bp,asize);
	
	// set free block header and footer and epilogue header
	put(p_to_header(bp), pack(asize, 0));
	put(p_to_footer(bp), pack(asize, 0));
	put(p_to_header(next_bp(bp)), pack(0,1));
	return coalesce(bp);
}

// function that combines adjacent free blocks into one larger free block
// and remove the appropriate free blocks from the list
static blk_ptr coalesce(void *bp){
	// maintain information of previous and next block
	size_t prev_alloc = get_alloc(p_to_header(prev_bp(bp)));
	size_t next_alloc = get_alloc(p_to_header(next_bp(bp)));
	size_t size = get_size(p_to_header(bp));
	
	// case that previous and next block allocated return current bp
	if(prev_alloc && next_alloc){
		return bp;
	}
	// previous block is free
	if(!prev_alloc && next_alloc){
		// get previous block info
		size += get_size(p_to_header(prev_bp(bp)));

		// delete current free block and previous block from the seg list
		delete_list_blcok(bp);
		delete_list_blcok(prev_bp(bp));

		// update block info 
		put(p_to_footer(bp),pack(size,0));
		put(p_to_header(prev_bp(bp)),pack(size,0));
		bp = prev_bp(bp);
	}
	// next block is free
	else if(prev_alloc && !next_alloc){
		// get next block info
		size += get_size(p_to_header(next_bp(bp)));

		// delete current free block and next block from the seg list
		delete_list_blcok(bp);
		delete_list_blcok(next_bp(bp));

		// update block info 
		put(p_to_header(bp),pack(size, 0));
		put(p_to_footer(bp),pack(size, 0));
	}
	// both of previous and next blocks are free
	else{
		// get size of blocks
		size += get_size(p_to_footer(next_bp(bp))) + get_size(p_to_header(prev_bp(bp)));

		// delete current, previous and next block from the seg list
		delete_list_blcok(bp);
		delete_list_blcok(next_bp(bp));
		delete_list_blcok(prev_bp(bp));

		// update block info
		put(p_to_footer(next_bp(bp)),pack(size,0));
		put(p_to_header(prev_bp(bp)),pack(size,0));
		bp = prev_bp(bp);
	}

	// add new free block to seg list
	add_list_block(bp,size);
	return bp;
}

// function that search the segregated list to find the appropriate size class
// and return the size class index of the segregated list
static int search_seg_list(size_t size){
	if(size < seg_size_class1)	return 0;
	else if((size >= seg_size_class1) && (size < seg_size_class2))	return 1;
	else if((size >= seg_size_class2) && (size < seg_size_class3))	return 2;
	else if((size >= seg_size_class3) && (size < seg_size_class4))	return 3;
	else if((size >= seg_size_class4) && (size < seg_size_class5))	return 4;
	else if((size >= seg_size_class5) && (size < seg_size_class6))	return 5;
	else if((size >= seg_size_class6) && (size < seg_size_class7))	return 6;
	else if((size >= seg_size_class7) && (size < seg_size_class8))	return 7;
	else if((size >= seg_size_class8) && (size < seg_size_class9))	return 8;
	else if((size >= seg_size_class9) && (size < seg_size_class10))	return 9;
	else if((size >= seg_size_class10) && (size < seg_size_class11))	return 10;
	else if((size >= seg_size_class11) && (size < seg_size_class12))	return 11;
	else if((size >= seg_size_class12) && (size < seg_size_class13))	return 12;
	else	return 13;
}

// function that place the requested block into free block
// compute the remainning size of the free block, if it is less 
// or equal to the min free block size, then allocate free block
// and add to the list.
static blk_ptr place(blk_ptr bp, size_t asize){
	// delete the free block from seg list
	delete_list_blcok(bp);

	size_t csize = get_size(p_to_header(bp));
	size_t *next_block;

	// compare the remaining block size to the min free block size
	// if large than or equal to the min free block size, then split the block
	if((csize - asize) >= (MIN_BLOCK_SIZE)){
		put(p_to_header(bp), pack(asize,1));
		put(p_to_footer(bp), pack(asize,1));
		next_block = next_bp(bp);
		put(p_to_header(next_bp(bp)), pack(csize-asize,0));
		put(p_to_footer(next_bp(bp)), pack(csize-asize,0));
		add_list_block(next_bp(bp), csize-asize);
	}

	// if the remaining size is not larger than min block size, 
	// then assign free block to allocated
	else{
		put(p_to_header(bp), pack(csize, 1));
		put(p_to_footer(bp), pack(csize, 1));
		if (!get_alloc(p_to_header(next_block)))
			put(p_to_footer(next_block), get(p_to_header(next_block)));
	}
	return bp;
}

// function that remove the block from the segregated list given
// pointer and fix the the pointers
static void delete_list_blcok(blk_ptr bp){
	// get block size info
	size_t size = get_size(p_to_header(bp));

	// search for size class index
	int seg_index = search_seg_list(size);
	
	if(prev_listbp(bp) == NULL){
		// update previous free block pointer 
		if(next_listbp(bp) != NULL){
			putptr(prev_freebp(next_listbp(bp)), NULL);
			seg_list[seg_index] = next_listbp(bp);
		}
		else{
			seg_list[seg_index] = NULL;
		}

	}
	else{
		// update previous free block and next free pointer 
		if(next_listbp(bp) != NULL){
			putptr(prev_freebp(next_listbp(bp)), prev_listbp(bp));
			putptr(next_freebp(prev_listbp(bp)), next_listbp(bp));
			
		}
		else{
			putptr(next_freebp(prev_listbp(bp)), NULL);
		}

	}

}

// function that insert the free block into segregated list
static void add_list_block(blk_ptr bp, size_t size){
	// find the appropirate size class list
    int seg_index = search_seg_list(size);

	// set head of the size class list
    void *curr_head_ptr = curr_head_ptr = seg_list[seg_index]; 

 // case that no blocks in the size list
    if (curr_head_ptr != NULL) { 
		// set bp to list head and update the previous and next block info
		seg_list[seg_index] = bp;
        putptr(prev_freebp(bp), NULL);
        putptr(next_freebp(bp), curr_head_ptr);
        putptr(prev_freebp(curr_head_ptr), bp);
        
    }
	// case that there are blocks in the size list
    else { 
		// set bp to the list head and set previous and next free block to NULL
		seg_list[seg_index] = bp;
		putptr(prev_freebp(bp), NULL);
        putptr(next_freebp(bp), NULL);  
    }
}


/*
 * Initialize: return false on error, true on success.
 */
// function that initialize the heap and the segregated list 
// and create prologue and epilogue blocks
bool mm_init(void)
{
	for(int i = 0; i < SEG_LIST_SIZE; i++){
		seg_list[i] = NULL;
	}
		
	// create the prologue and epilogue
	if((heap_list_ptr = mem_sbrk(MIN_BLOCK_SIZE)) == NULL){
		return false;
	}

	// create header and footer prologue
	put(heap_list_ptr, 0);
	put(heap_list_ptr + HEADER_SIZE, pack(2*HEADER_SIZE,1));
	put(heap_list_ptr + (2*FOOTER_SIZE), pack(2*FOOTER_SIZE, 1));

	// create free blocks in the heap
	if(extend_heap(EXTEND_SIZE) == NULL){
		return false;
	}

	return true;

}

/*
 * malloc: return a pointer to the payload of the allocated block
 * search the segregated list for free block and extend the heap if 
 * more blocks are required.
 */
void* malloc(size_t size)
{
	blk_ptr bp = NULL;
	size_t asize;
	size_t extendsize;
	int seg_index = 0;
	
	// check if size is valid
	if(size == 0){
		return NULL;
	}
	
	// Modify block size to include header 
	if(size <= HEADER_SIZE*2){
		asize = MIN_BLOCK_SIZE;
	}
	// alignment request
	else{
		asize = align(size + HEADER_SIZE*2);
	}

	// find the right size class index
	seg_index = search_seg_list(asize);
	// decide extended size for heap
	extendsize = max(asize, EXTEND_SIZE);

	// find the right spot to place the block
	if(seg_index != SEG_LIST_SIZE){
		bp = seg_list[seg_index];
		if(bp != NULL){
			for(int i = 0; i < MIN_BLOCK_SIZE; i++){
				if(bp == NULL){
					break;
				}
				if(asize <= get_size(p_to_header(bp))){
					place(bp,asize);
					return bp;
				}
				bp = next_listbp(bp);
			}
		}
	}

	seg_index++;
	bp = NULL;
	
	// if there is no room in the list allocate more memory in heap by min block size
	while((seg_index < SEG_LIST_SIZE) && (bp == NULL)){
		bp = seg_list[seg_index];
		seg_index++;
	}
	
	if(bp == NULL){
		bp = extend_heap(extendsize);
	}

	bp = place(bp,asize);
	return bp;
}

/*
 * free: free the block and add to the list
 */
void free(void* ptr)
{
	size_t size;
   	if(ptr == NULL)
			return;

	size = get(p_to_header(ptr));
	// set header and footer of the block to unallocated
	put(p_to_header(ptr),pack(size, 0));
	put(p_to_footer(ptr),pack(size, 0));

	// add to the list
	add_list_block(ptr, size);
	coalesce(ptr);
}

/*
 * realloc: return a new pointer that has the size and content of the old pointer
 * malloc space for the new pointer
 */
void* realloc(void* oldptr, size_t size)
{
	// new pointer
	blk_ptr newptr;

	// call equivalent to malloc(size)
	if(oldptr == NULL){
		return malloc(size);
	}
	
	// call equivalent free(oldptr) if size is 0
	if(size == 0){
		free(oldptr);
		return NULL;
	}

	// malloc space and copy the content of oldptr
	newptr = malloc(size);
	size_t copysize = min(size, get_size(p_to_header(oldptr)) - HEADER_SIZE);
	memmove(newptr,oldptr,copysize);
	free(oldptr);
	return newptr;

}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ret;
    size *= nmemb;
    ret = malloc(size);
    if (ret) {
        memset(ret, 0, size);
    }
    return ret;
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * commented out for submission. 
 * checks both the heap and the free list
 */

bool mm_checkheap(int lineno)
{
	#ifdef DEBUG
	printf("Enter checkheap\n");
    size_t size = 0;
    heap_list_ptr = mem_heap_lo() + 2*HEADER_SIZE;
    while (get_size(p_to_header(heap_list_ptr)) != 0){
		// check for size
        size = get_size(p_to_header(heap_list_ptr));
        if (size != get_size(p_to_footer(heap_list_ptr))){
            printf("Header and footer size mismatch\n");
        }

        //check for adjacent free block 
        if (!get_alloc(p_to_header(heap_list_ptr))){
            if (!get_alloc(p_to_header(next_bp(heap_list_ptr)))){
                printf("Found adjacent block\n");
            }
        }

        heap_list_ptr = heap_list_ptr + size;
    }

	#endif /* DEBUG */
    return true;
}




