/*
 * mm.c - A dynamic memory management implementation that uses an
 *        implicit free list.
 * 
 * In this approach, a block is allocated by simply incrementing
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
    "POWERHAUS",
    /* First member's full name */
    "Vyas Alwar",
    /* First member's email address */
    "VyasAlwar2018@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Chung Ho Lee",
    /* Second member's email address (leave blank if none) */
    "ChungLee2018@u.northwestern.edu"
};
/* Set to 1 to print heap information */
#define HEAP_CHECKER 0
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define PTR_SIZE (sizeof(void *))

#define WSIZE 4 //Word size in bytes. Also header/footer size
#define DSIZE 8 //Double word size in bytes
#define CHUNKSIZE (1<<12) // Page size in bytes


/* gets the maximum or minimum of two values*/
#define MAX(x, y) ((x) > (y)? (x) : (y)) 
#define MIN(x, y) ((x) < (y)? (x) : (y)) 

/*packs size and alloc into one word */
#define PACK(size, alloc) ((size) | (alloc)) 

/*get or put a word at p*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/*gets the size and allocation bit from a header pointer*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Returns header and footer pointers given a block on the heap*/
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Gets address of next and previous blocks given a block pointer*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

typedef struct freelink Link;
struct freelink {
    Link *prev;
    Link *next;
};


/*In a free block, gets pointers to the the next and previous free block block*/
//#define NEXT_FREE_BLKP(bp) (GET(bp))
//#define PREV_FREE_BLKP(bp) (GET((char *)((bp) + PTR_SIZE)))
//
///*In a free block, store next and previous pointers*/
//#define STORE_NEXT_BLKP(bp, next) (*(NEXT_FREE_BLKP((bp))=next)
//#define STORE_PREV_BLKP(bp, next) (*(PREV_FREE_BLKP((bp))=next)
/*
 * Signatures
 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int mm_check(void);
static void connect(Link *prev, Link *next);

static void *heap_listp;
static Link *root; //Prev-most free block
static Link *top; //Next-most free block
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    root = NULL;
    top = NULL;
    heap_listp = mem_sbrk(4*WSIZE);
    /* Create the initial empty heap */
    if (heap_listp == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp+=(2*WSIZE);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE)== NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size){
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else 
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit((asize))) != NULL) {
            place(bp, asize);
            if (HEAP_CHECKER){
                printf("Heap information: malloc fit found\n");
                mm_check();
            }
            return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    if (HEAP_CHECKER){
        printf("Heap information: malloc fit not found\n");
        mm_check();
    }
    return bp;
}

/*
 * mm_free - 
 */
void mm_free(void *ptr)
{
    //printf("mm_free called with 0x%x\n", (unsigned int)ptr);
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    Link *thislink = (Link *)ptr;
    //Search for predecessors
    if (root == NULL){
        connect(NULL, thislink);
        connect(thislink, NULL);
    }
    else {
        Link *bp;

        for (bp=root; bp->next!=NULL; bp=bp->next){
            if (((unsigned int)bp < (unsigned int)ptr) && ((unsigned int)(bp->next) > (unsigned int)ptr)){
                connect(thislink, bp->next);
                connect(bp, thislink);
                break;
            }
        }
        //if (bp==top && bp==root){
            //bp is the top and the root.
            if (((unsigned int)thislink) > (unsigned int)top) {
                connect(top, thislink);
                connect(thislink, NULL);
            }
            else if (((unsigned int)thislink) < (unsigned int)root) {
                connect(thislink, root);
                connect(NULL, thislink);
            }
        //}
    }
    coalesce(ptr);
    if (HEAP_CHECKER){
        printf("Heap information: free\n");
        mm_check();
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
/*
 * Helper Functions
 */


static void *extend_heap(size_t words){
    void  *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    

    //printf("%d\n", size);
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));  /* Free block header */
    /* Link the free blocks */
    Link *new_link = (Link *) bp;
    connect(top, new_link); 
    /*If top is NULL, the next two lines are redundant*/
    top = new_link;
    new_link->next = NULL;
    if (root == NULL)
        root = new_link;

    PUT(FTRP(bp), PACK(size, 0)); /* Free blook footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*New epilogue header */

    return coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    Link *thislink = (Link *)bp;
    Link *prev = thislink -> prev;
    Link *next = thislink -> next;

    if (prev_alloc && next_alloc){
        //printf("Case 1\n");
        return bp;
    }

    else if (prev_alloc && !next_alloc){
        //printf("Case 2\n");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        if (next != NULL)
            connect(thislink, next->next);
        else
            connect(thislink, NULL);
    }

    else if (!prev_alloc && next_alloc){
        //printf("Case 3\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        connect(prev, next);
    }

    else {
        //printf("Case 4\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        connect(prev, next->next);
    }
    return bp;
}

static void *find_fit(size_t asize){
    Link *bp; //initialize to free root
    if (root == NULL) // No free blocks
        return NULL;
    for (bp = root; bp != NULL; bp = bp->next){
        if (asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    //printf("\tPlace called with: 0x%x\n", (unsigned int)bp);
    size_t csize  = GET_SIZE(HDRP(bp));
    Link *thislink = (Link *)bp;
    Link *next = thislink->next;
    Link *prev = thislink->prev;
    if ((csize - asize) >= (2 * DSIZE)){
        //printf("\n\nSplitting occurs!\n\n");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        // Fill splitted free block
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        /* Linking shit up */
        thislink = (Link *)bp;
        //printf("\tthislink: 0x%x\n", (unsigned int)thislink);
        //printf("\tnextlink: 0x%x\n", (unsigned int)next);
        //printf("\tprevlink: 0x%x\n", (unsigned int)prev);
        connect(prev, thislink);
        connect(thislink, next);
    }
    else { //Fill the block
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        if (prev != NULL && next != NULL){
            connect(prev, next);
        }
        else if (prev == NULL && next != NULL){ //root
            next -> prev = NULL;
            root = next;
        }
        else if (prev != NULL && next == NULL){ //top
            prev->next = NULL;
            top = prev;
        }
        else { //no free blocks
            root = NULL;
            top = NULL;
        }
    }
}
/*
 * connect: Links two nodes in the explicit free list together. NULL is treated
 *          as a terminating node, that is to say that if prev is NULL or next
 *          is NULL, calling connect is equivalent to setting the other
 *          argument to be the root or the top respectively.
 */
static void connect(Link *prev, Link *next){
    if (prev != NULL && next != NULL){
        prev->next = next;
        //printf("prev->prev: 0x%x\n", (unsigned int)(prev->prev));
        next->prev = prev;
    }
    else if (prev == NULL && next != NULL){
        /* Set next to be the root. */
        (next -> prev) = NULL;
        root = next;
    }
    else if (prev != NULL && next == NULL){
        //printf("\nAAAH!\n");
        prev -> next = NULL;
        top = prev;
    }
    else {
        return;
    }
}

/*
 * mm_check: a heap checker
 */
int mm_check(void){
    void *bp; int count = 0;
    printf("\tRoot Location: 0x%x\t\tTop location: 0x%x\t\t\n", (unsigned int)root, (unsigned int)top);
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        printf("\tBlock %d\n", count);
        printf("\t\tLOCATION 0x%x\n", (unsigned int)bp);
        printf("\t\tSIZE: %d\n", GET_SIZE(HDRP(bp)));
        printf("\t\tALLOC: %d\n", GET_ALLOC(HDRP(bp)));
        if (!GET_ALLOC(HDRP(bp))){
            printf("\t\t\tPrevious: 0x%x", (unsigned int)(((Link *)bp)->prev));
            printf("\t\t\tNext: 0x%x\n", (unsigned int)(((Link *)(bp))->next));
        }
        count++;
    }
    printf("\n");
    return 1;
}

