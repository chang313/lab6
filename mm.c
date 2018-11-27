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
#define MIN(x,y) ((x) < (y)? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) =(size_t) (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Address of free block's predecessor and successor entries */
#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + DSIZE)

/* Address of free block's predecessor and successor on the list */
#define PRED(bp) (*(char **)(PRED_PTR(bp)))
#define SUCC(bp) (*(char **)(SUCC_PTR(bp)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* heap consistency checker */
static int mm_check(void);


/* global variable */
static char *heap_listp;
static char *free_listp;

/* helper functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t size);
static void insert(void *bp);
static void delete(void *bp);

/* mm_check implementation */
static int mm_check(void) 
{ return 0;
}



/* hepler function implementation */

static void *extend_heap(size_t words) 
{ 
    char *bp;
    size_t size;

    /* ALlocate an even number of words to maintain alignmnent */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    bp = mem_sbrk(size);
    if ((long) bp == -1) 
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));  /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New epilogue header */
    
    /* insert the new free block to the free list */
    insert(bp);
   
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
// For given free block, if there exists prev or next free block,  coalesce with it and return the new free block pointer.
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));   
    
    /* Case 1: return the bp */
    if (prev_alloc && next_alloc) 
        return bp;
    /* delete the current free block from the free list */
    delete(bp);

    if (prev_alloc && !next_alloc) { /* Case 2 : delete the next block and insert new  block */
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 : delete original free block from the list and insert new block */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        delete(bp);
    }
    else if (!prev_alloc && !next_alloc) { /* Case 4 : delete both of prev and next block  */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        delete(PREV_BLKP(bp));
        delete(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    insert(bp);
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

// With given free block to be alocated soon, place the size block on the bp address
static void place(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));

    /* if original free block's remained size is bigger than MINIMUM */
    if ((old_size - size) >= MINIMUM) {
        PUT(HDRP(bp), PACK(size,1));
        PUT(FTRP(bp), PACK(size,1));
        delete(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK((old_size - size), 0));
        PUT(FTRP(bp), PACK((old_size - size), 0));
        insert(bp);
    } else {
        PUT(HDRP(bp), PACK(old_size, 1));
        PUT(FTRP(bp), PACK(old_size, 1));
        delete(bp);
    } 
}
 
// Insert the free block to the free linked list 
static void insert(void *bp) {
    if (free_listp == NULL) {
        PUT(PRED_PTR(bp), NULL);
        PUT(SUCC_PTR(bp), NULL);
        free_listp = bp;
    } else {
        PUT(PRED_PTR(bp), NULL);
        PUT(SUCC_PTR(bp), free_listp);
        PUT(PRED_PTR(free_listp), bp);
        free_listp = bp;
    }
}

// Delete the free block from the free linked list
static void delete(void *bp) {
    char *pred;
    char *succ;
    /* Get the predecessor and successor of bp */
    pred = PRED(bp);
    succ = SUCC(bp);
    /* Change the link of pred and succ */
    if (pred == NULL && succ == NULL) { /* if free list is empty */
        free_listp = NULL;
    } else if (pred == NULL) { /* if allocated free block is first entry of the list */
        free_listp = succ;
        PUT(SUCC_PTR(bp), NULL);
        PUT(PRED_PTR(succ), NULL);
    } else if (succ == NULL) { /* if allocated block is last entry of the list */
        PUT(SUCC_PTR(pred),  NULL);
        PUT(PRED_PTR(bp), NULL);
    } else { /* if the block is neither first or last of the list */
        PUT(SUCC_PTR(pred), succ);
        PUT(PRED_PTR(succ),  pred);
        PUT(SUCC_PTR(bp), NULL);         
        PUT(PRED_PTR(bp), NULL);
    }    
   
}


/* End of helper function implementation */

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    /* global variable initialization */
    free_listp = NULL;
  
    //printf("##########start###########\n");
    /* Create the initial empty heap */
    heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void *)-1)
        return -1;
    PUT(heap_listp, 0);	/* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); /* Epilogue header */
    heap_listp += 2*WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE byte */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* adjusted block size */ 
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp; 

    if (size == 0) 
        return NULL;
 
    /* Adjust block size to include overhead and alignment reqs. */
    asize = MAX(ALIGN(size+DSIZE), MINIMUM);
    //printf("malloc_sizse:	 [%d]\n", asize); 
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) !=NULL) {
        place(bp, asize);
        return bp;
    }


    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
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
    //printf("free_size:	 [%d]\n", size); 
    /* change the alloc bit to 0 */
    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    /* insert freed block into the free list */
    insert(ptr);
    /* coalesce the freed block */
    coalesce(ptr);
   //  printf("free_listp address:  [%p]\n", (void *)free_listp);
    //printf("free_listp footer address: [%p]\n", (void *)GET_SIZE(HDRP(free_listp)));
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;  
    size_t old_size;
    size_t new_size = ALIGN(size+DSIZE);
 
    if (ptr == NULL) { /* equivalent to mm_malloc */
        if (size == 0) {
            return NULL;
        }  
        /* Adjust block size to include overhead and alignment reqs. */
        asize = MAX(ALIGN(size+DSIZE), MINIMUM);
        //printf("malloc_sizse:      [%d]\n", asize); 

        /* Search the free list for a fit */
        if ((bp = find_fit(asize)) !=NULL) {
            place(bp, asize);
            return bp;
        }  


        /* No fit found. Get more memory and place the block */
        extendsize = MAX(asize, CHUNKSIZE);
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
            return NULL;
        place(bp, asize);
        return bp;

    } else if (size == 0) { /* if size=0, then it's equivalent to mm_free */
        /* change the alloc bit to 0 */
        old_size = GET_SIZE(HDRP(ptr));
        PUT(HDRP(ptr), PACK(old_size,0));
        PUT(FTRP(ptr), PACK(old_size,0));
        /* insert freed block into the free list */
        insert(ptr);
        /* coalesce the freed block */
        coalesce(ptr);
        
    } else {
       old_size = GET_SIZE(HDRP(ptr));   

       /* allocate new block */
  
       /* Search the free list for a fit */
       if ((bp = find_fit(new_size)) !=NULL) {
           place(bp, new_size); 
           memcpy(bp, ptr, MIN(old_size - DSIZE, size));
           /* Free the original block */
           PUT(HDRP(ptr), PACK(old_size,0));
           PUT(FTRP(ptr), PACK(old_size,0));
           insert(ptr);
           coalesce(ptr);
           return bp;
       }

       /* No fit found. Get more memory and place the block */
       extendsize = MAX(new_size, CHUNKSIZE);
       if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
           return NULL;
       place(bp, new_size);
       memcpy(bp, ptr, MIN(old_size - DSIZE, size));
       /* free the original block */
       PUT(HDRP(ptr), PACK(old_size,0));
       PUT(FTRP(ptr), PACK(old_size,0));
       insert(ptr);
       coalesce(ptr);

       return bp;     
    
    }
}

