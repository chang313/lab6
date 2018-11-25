/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"


/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) 
#define MINIMUM 24

#define MAX(x,y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = val)

#define GET_SISE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Address of free block's predecessor and successor entries */
#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)

/* Address of free block's predecessor and successor on the list */
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_PTR(bp)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* global variable */
static char *free_listp;

/* helper functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t size);
static void insert(void *bp);
static void delete(void *bp);

/* hepler function implementation */

static void *extend_heap(size_t words) 
{ 
    char *bp;
    size_t size;

    /* ALlocate an even number of words to maintain alignmnent */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { /* Case 1 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
   
}

static void *find_fit(size_t size) {
    void *ptr;
    ptr = free_listp;

    while (ptr != NULL) {
        if (GET_SIZE(HDRP(ptr)) >= size) {
            return ptr;
        }
        ptr = SUCC(ptr);
    } 

    return NULL;     
}

// Place the size block on the bp address
static void place(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));


    /* if original free block's remained size is bigger than MINIMUM */
    if ((old_size - size) >= MINIMUM) {
        PUT(HDRP(bp), PACK(size,1));
        PUT(FTRP(bp), PACK(size,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(old_size - size, 0));
        PUT(FTRP(bp), PACK(old_size - size, 0));
        insert(bp);
    } else {
        PUT(HDRP(bp), PACK(old_size, 1));
        PUT(FTRP(bp), PACK(old_size, 1));
    } 
}

// Insert the free block to the free linked list 
static void insert(void *bp) {
    if (free_listp == NULL) {
        PRED(bp) = NULL;
        SUCC(bp) = NULL;
        free_listp = bp;
    } else {
        PRED(bp) = NULL;
        SUCC(bp) = free_listp;
        PRED(free_listp) = bp;
        free_listp = bp;
    }
}

// Delete the free block from the free linked list
static void delete(void *bp) {
    void *pred;
    void *succ;

    pred = PRED(bp);
    succ = SUCC(bp);
    
    SUCC(pred) = succ;
    PRED(succ) = pred;


}


/* End of helper function implementation */

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    char *heap_listp;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);	/* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); /* Epilogue header */
    head_listp += 2*WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE byte */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    free_listp = heap_listp + DSIZE;
    PRED(free_listp) = NULL;
    SUCC(free_listp) = NULL;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /*
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */
    size_t asize; /* adjusted block size */ 
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp; 

    if (size == 0) 
        return NULL;
 
    /* Adjust block size to include overhead and alignment reqs. */
    size = MAX(ALIGN(size+DSIZE), MINIMUM);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) !=NULL) {
        delete(bp);
        place(bp, asize);
        return bp;
    }


    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize(WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
        
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    /* change the alloc bit to 0 */
    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    /* insert freed block into the free list */
    insert(ptr);
    /* coalesce the freed block */
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t asize;
    void *new_ptr = mm_malloc(size);

    if (ptr == NULL) {
        return new_ptr;
    } else if (size == 0) {
        mm_free(ptr);
        return;
    }
    asize = MAX(ALIGN(size+DSIZE), MINIMUM);
    if (asize == old_size) {
        return ptr; 

    } else if (old_size > asize) {
        if ((old_size-asize) >= MINIMUM) {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            ptr = NEXT_BLKP(ptr);
            PUT(HDRP(ptr), PACK(old_size-asize, 0));
            PUT(FTRP(ptr), PACK(old_size-asize, 0));
            insert(ptr);
        } else {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1)); 
        }
        return ptr;
        
    } else {
        return new_ptr;
    }
}






