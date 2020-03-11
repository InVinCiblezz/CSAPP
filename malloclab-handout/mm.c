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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
        /* Team name */
        "Assignment 47",
        /* First member's full name */
        "Zhen ZHANG",
        /* First member's email address */
        "zhenzhang2019@u.northwestern.edu",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's email address (leave blank if none) */
        ""
};
#define DEBUG 1
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define LISTLENGTH 16

/* rounds up to the nearest multiple of ALIGNMENT */

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define OVERHEAD    8
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */
#define INITSIZE (1<<6) /* Extend heap by this amount (bytes) in init*/

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define SUCC(p) ((char *)(p) + WSIZE)
/* Given block ptr p, set the pred and succ address */
#define PUT_PRED(p, val) (PUT((char *)(p), val))
#define PUT_SUCC(p, val) (PUT(SUCC(p), val))

/* Read the pred and succ from address p */
#define GET_PRED(p) (*(char **)(p))
#define GET_SUCC(p) (*(char **)SUCC(p))

char *heap_listp;
static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void realloc_place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *realloc_coalesce(void *bp, size_t newSize, int *isNextFree);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);
static size_t get_asize(size_t size);
void *seg_lists[LISTLENGTH];
static void checklist();

/*
 * extend_heap - extend the heap when it is full.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */

    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

    /* Coalesce if the previous block was free include insert*/
    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)//done
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0);                                 /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          /* Epilogue header */
    heap_listp += (2 * WSIZE);
    int i = 0;
    for (; i < LISTLENGTH; i++) {
        seg_lists[i] = NULL;
    }
    /* Extend the empty heap with a free block of INITSIZE bytes */
    if (extend_heap(INITSIZE/WSIZE) == NULL)
        return -1;
    #ifdef DEBUG
        checklist();
    #endif
        return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize, size_list;    /* Adjusted block size */
    size_t extendsize;          /* Amount to extend heap if no fit */
    char *bp = NULL;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    asize = get_asize(size);
    size_list = asize;
    int index = 0;
    for (; index < LISTLENGTH; index++, size_list >>= 1) { // find index in seg_list
        if ((size_list > 1) || (seg_lists[index] == NULL))
            continue;
        char *i = seg_lists[index];
        for(; i != NULL; i = GET_SUCC(i)) {
            if (GET_SIZE(HDRP(i)) < asize)
                continue;
            bp = i;
            break;
        }
        if (bp != NULL)
            break;
    }
    if (bp == NULL) {
        /* No fit found. Get more memory and place the block */
        extendsize = MAX(asize,CHUNKSIZE);
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
            return NULL;
    }
    #ifdef DEBUG
        checklist();
    #endif
        return place(bp, asize);
}
/*
 * place - place block.
 *     Always return the place address
 */
static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    delete_node(bp);
    if ((csize - asize) < (DSIZE + OVERHEAD)) {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        return bp;
    } else if (asize >= 96) {
        PUT(HDRP(bp), PACK((csize - asize), 0));
        PUT(FTRP(bp), PACK((csize - asize), 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK((asize), 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK((asize), 1));
        insert_node(bp, csize - asize);
        return NEXT_BLKP(bp);
    }
    else {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
        insert_node(NEXT_BLKP(bp), csize - asize);
        return bp;
    }
}
/*
 * coalesce - coalesce free blocks.
 *
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {        /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_node(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {   /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_node(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc){   /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp, size);
    #ifdef DEBUG
        checklist();
    #endif
        return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
    #ifdef DEBUG
        checklist();
    #endif
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *newptr;
    size_t copySize = GET_SIZE(HDRP(ptr));
    size_t asize = get_asize(size);
    if(copySize > asize) {          // just replace
        realloc_place(ptr, asize);
        return ptr;
    } else if (copySize == asize){  // just return
        return ptr;
    } else {
        int isNextFree;
        char *bp = realloc_coalesce(ptr, asize, &isNextFree);
        // next block is free
        if(isNextFree == 1){
            realloc_place(bp, asize);
        } else if(isNextFree == 0 && bp != ptr){
            memcpy(bp, ptr, size);
            realloc_place(bp, asize);
        }else{
            newptr = mm_malloc(size);
            memcpy(newptr, ptr, size);
            mm_free(ptr);
            return newptr;
        }
        return bp;
    }
}
/*
 * realloc_place - place block.
 *
 */
static void realloc_place(void *bp,size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp),PACK(csize,1));
    PUT(FTRP(bp),PACK(csize,1));
}

/*
 * realloc_coalesce - coalesce free blocks.
 *
 */
static void *realloc_coalesce(void *bp, size_t newSize, int *isNextFree)
{
    size_t  prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t  next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    *isNextFree = 0;
    /*coalesce the block and change the point*/
    if(prev_alloc && !next_alloc) {                     /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if(size >= newSize) {
            delete_node(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(size, 1));
            PUT(FTRP(bp), PACK(size, 1));
            *isNextFree = 1;
        }
    }
    else if(!prev_alloc && next_alloc) {                /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        if(size >= newSize) {
            delete_node(PREV_BLKP(bp));
            PUT(FTRP(bp), PACK(size, 1));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
            bp = PREV_BLKP(bp);
        }
    }
    else if(!prev_alloc && !next_alloc) {               /* Case 4 */
        size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        if(size >= newSize) {
            delete_node(NEXT_BLKP(bp));
            delete_node(PREV_BLKP(bp));
            PUT(FTRP(NEXT_BLKP(bp)),PACK(size, 1));
            PUT(HDRP(PREV_BLKP(bp)),PACK(size, 1));
            bp = PREV_BLKP(bp);
        }
    }
    return bp;
}
/*
 * insert_node - insert the node from seg_lists.
 *
 */
static void insert_node(void *bp, size_t size)
{
    int index = 0;
    size_t list_size = size;
    for (; (list_size > 1) && (index < LISTLENGTH - 1); index++) {
        list_size >>= 1;
    }
    char *i = seg_lists[index];
    char *pre = NULL;
    while ((i != NULL) && (size > GET_SIZE(HDRP(i)))) {
        pre = i;
        i = GET_SUCC(i);
    }
    if (i == NULL && pre == NULL) {
        seg_lists[index] = bp;
        PUT_PRED(bp, NULL);
        PUT_SUCC(bp, NULL);
    } else if (i == NULL && pre != NULL) {
        PUT_PRED(bp, pre);
        PUT_SUCC(bp, NULL);
        PUT_SUCC(pre, bp);
    } else if (pre == NULL) {
        seg_lists[index] = bp;
        PUT_PRED(i, bp);
        PUT_SUCC(bp, i);
        PUT_PRED(bp, NULL);
    } else {
        PUT_PRED(bp, pre);
        PUT_SUCC(bp, i);
        PUT_PRED(i, bp);
        PUT_SUCC(pre, bp);
    }
    #ifdef DEBUG
        checklist();
    #endif
}

/*
 * delete_node - delete the node from seg_lists.
 *
 */
static void delete_node(void *bp)//done
{
    size_t list_size = GET_SIZE(HDRP(bp));
    int index = 0;
    for (; (list_size > 1) && (index < LISTLENGTH - 1); index++) {
        list_size >>= 1;
    }
    if (GET_PRED(bp) == NULL) {
        seg_lists[index] = GET_SUCC(bp);
        if (GET_SUCC(bp) != NULL)
            PUT_PRED(GET_SUCC(bp), NULL);
    } else if (GET_SUCC(bp) == NULL) {
        PUT_SUCC(GET_PRED(bp), NULL);
    } else {
        PUT_SUCC(GET_PRED(bp), GET_SUCC(bp));
        PUT_PRED(GET_SUCC(bp), GET_PRED(bp));
    }
    #ifdef DEBUG
        checklist();
    #endif
}

/* Adjust block size to include overhead and alignment reqs. */
static size_t get_asize(size_t size)
{
    size_t asize;
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);
    return asize;
}
/* Check the status of list. */
static void checklist()
{
    int index = 0;
    for(;index < LISTLENGTH; index++){
        char *i = seg_lists[index];
        while(i != NULL){
            printf("seg list %d, addr %p, size %d, next %p, prev %p\n", index, i, GET_SIZE(HDRP(i)), GET_SUCC(i), GET_PRED(i));
            i = GET_SUCC(i);
        }
    }
}