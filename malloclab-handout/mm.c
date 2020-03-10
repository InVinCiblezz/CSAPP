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
/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#ifdef DEBUG
# define DBG_PRINTF(...) printf(__VA_ARGS__)
# define dbg_printblock(bp) printblock(bp)
#else
# define DBG_PRINTF(...)
# define dbg_printblock(bp)
#endif

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define LISTLENGTH 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE	    4           /* Word and header/footer size (bytes) */
#define DSIZE		8           /* Double word size (bytes) */
#define OVERHEAD    8
#define CHUNKSIZE	(1<<12)     /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & (~0x7))
#define GET_ALLOC(p)    (GET(p) & 0x1)

#define SUCC(p) ((char *)(p) + WSIZE)
/* Given block ptr p, set the pred and succ address */
#define PUT_PRED(p, val) (PUT((p), (unsigned int)(val)))
#define PUT_SUCC(p, val) (PUT(SUCC(p), (unsigned int)(val)))

/* Read the pred and succ from address p */
#define GET_PRED(p) ((char *)GET(p))
#define GET_SUCC(p) ((char *)GET(SUCC(p)))

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

char *heap_listp;
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void realloc_place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *realloc_coalesce(void *bp, size_t newSize, int *isNextFree);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);
static int get_index(size_t size);
static size_t get_asize(size_t size);
void *seg_lists[LISTLENGTH];
//fine
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* fine
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));
    heap_listp += 2 * WSIZE;
    int i = 0;
    for(; i < LISTLENGTH; ++i)
        seg_lists[i] = NULL;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    CHECKHEAP(1);
    return 0;
}

/* fine
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;           /* Adjusted block size */
    size_t extendsize;      /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    asize = get_asize(size);
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    CHECKHEAP(1);
    return bp;
}

/* find fit bp in the seg_list */
static void *find_fit(size_t asize)
{
    int index = get_index(asize);
    for (; index < LISTLENGTH; index++) {
        char *i = seg_lists[index];
        for(; i != NULL; i = GET_SUCC(i)) {
            if (GET_SIZE(HDRP(i)) >= asize) {
                return i;
            }
        }

    }
    return NULL;
}
//fine
static void place(void *bp, size_t asize)
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

static void realloc_place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
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
    CHECKHEAP(1);
}
//fine
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {                        /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_node(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_node(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else if (!prev_alloc && !next_alloc) {                /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp, size);
    return bp;
}

static void *realloc_coalesce(void *bp, size_t newSize, int *isNextFree)
{
    size_t  prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t  next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    *isNextFree = 0;

    if(prev_alloc && !next_alloc) {                    /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if(size >= newSize) {
            delete_node(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(size, 1));
            PUT(FTRP(bp), PACK(size, 1));
            *isNextFree = 1;
        }
    } else if(!prev_alloc && next_alloc) {                /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        if(size >= newSize) {
            delete_node(PREV_BLKP(bp));
            PUT(FTRP(bp), PACK(size, 1));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
            bp = PREV_BLKP(bp);
        }
    } else if(!prev_alloc && !next_alloc) {               /* Case 4 */
        size += GET_SIZE(FTRP(NEXT_BLKP(bp)))+ GET_SIZE(HDRP(PREV_BLKP(bp)));
        if(size >= newSize) {
            delete_node(PREV_BLKP(bp));
            delete_node(NEXT_BLKP(bp));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
            bp = PREV_BLKP(bp);
        }
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize, asize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    asize = get_asize(size);
    copySize = GET_SIZE(HDRP(oldptr));

    if (asize < copySize) {    // just replace
        realloc_place(ptr, asize);
        return ptr;
    } else if (asize == copySize) { //just return
        return ptr;
    }
    else {
        int isNextFree;
        newptr = realloc_coalesce(ptr, asize, &isNextFree);
        if(isNextFree == 1){ // next block is free
            realloc_place(newptr, asize);
        } else if(isNextFree == 0 && newptr != ptr){ // prev block is free
            memcpy(newptr, ptr, size);
            realloc_place(newptr, asize);
        }else{  // realloc_coalesce failed
            newptr = mm_malloc(size);
            memcpy(newptr, ptr, size);
            mm_free(oldptr);
        }
        return newptr;
    }

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
//fine
static void insert_node(void *bp, size_t size)
{
    int index = get_index(size);
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
}
//fine
static void delete_node(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_index(size);

    if (GET_PRED(bp) == NULL) {
        seg_lists[index] = GET_SUCC(bp);
        if (GET_SUCC(bp) != NULL)
            PUT_PRED(GET_SUCC(bp), NULL);
    } else if (GET_SUCC(bp) == NULL) {
        if (GET_PRED(bp) != NULL)
            PUT_SUCC(GET_PRED(bp), NULL);
    } else {
        PUT_SUCC(GET_PRED(bp), GET_SUCC(bp));
        PUT_PRED(GET_SUCC(bp), GET_PRED(bp));
    }
}

static int get_index(size_t size){
    int index = 0;
    size_t list_size = size;
    for (; (list_size > 1) && (index < LISTLENGTH - 1); index++) {
        list_size >>= 1;
    }
    return index;
}

void mm_checkheap(int);
/* below code if for check heap invarints */

static void printblock(void *bp)
{
    long int hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'));
}

static int checkblock(void *bp)
{
    //area is aligned
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    //header and footer match
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
    size_t size = GET_SIZE(HDRP(bp));
    //size is valid
    if (size % 8)
        printf("Error: %p payload size is not doubleword aligned\n", bp);
    return GET_ALLOC(HDRP(bp));
}

static void printlist(void *i, long size)
{
    long int hsize, halloc;

    for(;i != NULL;i = SUCC(i))
    {
        hsize = GET_SIZE(HDRP(i));
        halloc = GET_ALLOC(HDRP(i));
        printf("[listnode %ld] %p: header: [%ld:%c] prev: [%p]  next: [%p]\n",
               size, i,
               hsize, (halloc ? 'a' : 'f'),
               PRED(i), SUCC(i));
    }
}
static void checklist(void *i, size_t tar)
{
    void *pre = NULL;
    long int hsize, halloc;
    for(;i != NULL;i = SUCC(i))
    {
        if (PRED(i) != pre) printf("Error: pred point error\n");
        if (pre != NULL && SUCC(pre) != i) printf("Error: succ point error\n");
        hsize = GET_SIZE(HDRP(i));
        halloc = GET_ALLOC(HDRP(i));
        if (halloc) printf("Error: list node should be free\n");
        if (pre != NULL && (GET_SIZE(HDRP(pre)) > hsize))
            printf("Error: list size order error\n");
        if (hsize < tar || ((tar != (1<<15)) && (hsize > (tar << 1)-1)))
            printf("Error: list node size error\n");
        pre = i;
    }
}
/*
 * mm_checkheap - Check the heap for correctness
 */
void mm_checkheap(int verbose)
{
    checkheap(verbose);
}
//heap level
void checkheap(int verbose)
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    // block level
    checkblock(heap_listp);
    int pre_free = 0;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        int cur_free = checkblock(bp);
        //no contiguous free blocks
        if (pre_free && cur_free) {
            printf("Contiguous free blocks\n");
        }
    }
    //list level
    int i = 0, tarsize = 1;
    for (; i < LISTMAX; i++) {
        if (verbose)
            printlist(seg_free_lists[i], tarsize);
        checklist(seg_free_lists[i],tarsize);
        tarsize <<= 1;
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}













