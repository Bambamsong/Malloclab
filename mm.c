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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 1. 매크로 정의하기

/* Basic constants and macros */
#define WSIZE   4                   /* 워드와 헤더/풋터의 크기 (바이트) */
#define DSIZE   8                   /* 더블워드의 사이즈 (바이트) */
// << : 지정한 수만큼 비트들을 전부 왼쪽으로 이동시킴
#define CHUNKSIZE (1<<12)           /* 힙확장 2진수에서 첫번째칸에 1이 채워져있는데 이걸 왼쪽으로 12칸 이동하게 되면 1000000000000(2)로 표현이됨 */
#define MAX(x,y) ((x) > (y)? (x) : (y)) /* 삼항연산자를 사용하여 비교하기 */
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) /* bit의 or 연산 */

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p)) /* unsigned int는 양수만 저장함 */
#define PUT(p, val) (*(unsigned int *)(p) =  (val))

/* Read the size and allocated fields from address p 사이즈를 읽고, 주소p로 영역을 할당 */
#define GET_SIZE(p) (GET(p) & ~0x7) /* Not 연산 ex) 0111 -> 1111~11000 / 마지막 3비트를 제거하여 블록 크기 가져옴 */
#define GET_ALLOC(p) (GET(p) & 0x1) /* 주어진 값의 마지막 비트만 남기고 나머지를 제거하여 할당 여부를 가져오는 역할 */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE) /* header 계산 */
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* Footer 계산  그림 그리기! */ 







/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if 
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














