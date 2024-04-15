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
#define PUT(p, val) (*(unsigned int *)(p) = (int)(val)) //블록의 주소를 담는다. 위치를 담아야지 나중에 헤더나 푸터를 읽어서 이동 혹은 연결 할 수 있음

/* Read the size and allocated fields from address p 사이즈를 읽고, 주소p로 영역을 할당 */
#define GET_SIZE(p) (GET(p) & ~0x7) /* Not 연산 ex) 0111 -> 1111~11000 / 마지막 3비트를 제거하여 블록 크기 가져옴  메모리 블록의 크기를 가져오는 매크로 */
// GET_SIZE 할당된 메모리 블록의 전체 크기를 가져옴(헤더 + 블록 + 푸터 포함?)
#define GET_ALLOC(p) (GET(p) & 0x1) /* 주어진 값의 마지막 비트만 남기고 나머지를 제거하여 할당 여부를 가져오는 역할 */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE) /* header 계산 */
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* Footer 계산  그림 그리기! */ 


/* Given block ptr bp, compute address of next and previous blocks  */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)    -   WSIZE)))
/* (char * (bp) 는 주소가 아니라 해당 메모리 위치의 값(바이트)을 가져올 수 있음 */
/* 위 매크로의 경우 bp(block point)의 주소가 들어가면 해당주소가 위치한 바이트값을 내보내고
   블록포인트 바이트값 - 1워드(1블록) */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)    -   DSIZE)))

static char * heap_listp; // 처음에 사용할 가용블록 힙을 만들어줌
static char * start_nextfit;


static void *find_fit(size_t asize);
static void place(void * bp, size_t asize);
static void *extend_heap(size_t words);
static void *coalesce(void * bp);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{ 
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1){
        return -1;
    } //메모리 시스템에서 4워드를 가져와서 빈 가용 리스트를 만들수 있도록 초기화
    PUT(heap_listp, 0); // 지금부터 여기는 힙입니다                                  /* Aligment padding */ // 블록 생성시 넣는 padding을 한 워드 크기만큼 생성. heap_listp의 위치는 맨 처음
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));        /* Prologue header */  // 할당을(1) 할건데 8바이트 만큼 줄 것이다. -> 1 WSIZE 늘어난 시점부터 PACK에서 나온 사이즈를 줄 것이다.
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));        /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));            /* Epilogue header */
    heap_listp += (2*WSIZE);                            // Prologue header와 푸터 사이로 포인터를 옮긴다. header 뒤 위치. 다른블록에 가기위해서 항상(bp)를 가지고 따지니까!
    start_nextfit = heap_listp;

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // extend heap을 통해 시작할 때 한번 heap을 늘려줌. 늘리는 양은 상관없음. 
        return -1;
    return 0;
}


static void *extend_heap(size_t words){
    size_t size;
    char *bp;
    /* alignment 유지를 위해 짝수 개수의 words를 Allocate */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 홀수이면(1이나오니까) 앞에꺼, 짝수이면(0이 나오니까) 뒤에꺼. 홀수 일 때 +1 하는건 8의 배수 맞추기 위함인듯.
    // long 형 (정수형 타입에서 가장 큰 타입, 8byte의 크기를 가지고 있음)
    if ( (long)(bp = mem_sbrk(size)) == -1 ){
        return NULL;
    }
    // 사이즈를 늘릴 때마다 old brk는 과거의 mem_brk위치로 감.
    /* 가용 블록의 헤더와 푸터를 init하고 에필로그 헤더를 init */
    PUT(HDRP(bp), PACK(size, 0)); // 가용블록의 헤더를 생성. (프롤로그 블록이랑 헷갈리면 안됨)
    PUT(FTRP(bp), PACK(size, 0)); // 가용블록의 푸터를 생성. 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 블록을 추가했으니 Epilogure header를 새롭게 위치 조정해야함  HDRP : 포인터기준 한칸 앞
    // 처음 세팅의 의미 = bp를 헤더에서 읽은 사이즈만큼 이동하고, 앞으로 한칸 간다. 그 위치가 결국 늘린 블록 끝에서 한칸 간거라 Epilogue header 위치.

    /* 만약에 prev block이 free였다면, coalesce해라! */

    return coalesce(bp); // 처음에는 coalesc(블록을 연결하는 함수)를 할게 없지만 함수 재사용을 위해 리턴값으로 선언
}


static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 그전 블록으로 가서 블록의 가용여부를 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 그 뒷 블록의 가용 여부 확인
    size_t size = GET_SIZE(HDRP(bp)); // 지금 블록의 사이즈 확인

    if (prev_alloc && next_alloc){ // CASE 1 - 이전블록과 다음블록 모두 할당. 현재블록의 상태는 할당에서 가용으로 변경
        start_nextfit = bp;
        return bp; // 이미 free에서 가용이 되어있으니 여기선 따로 free 할 필요 없음
    }

    else if (prev_alloc && !next_alloc){ // CASE 2 - 이전 블록은 할당 상태, 다음블록은 가용 상태.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더를 보고 그 블록의 크기만큼 지금 블록의 사이즈에 추가함
        PUT(HDRP(bp), PACK(size, 0)); // 헤더 갱신(더 큰 크기로 put)
        PUT(FTRP(bp), PACK(size, 0)); // 푸터 갱신
    }

    else if (!prev_alloc && next_alloc){            // CASE 3 - 이전 블록은 가용상태, 다음블록은 할당 상태
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      // 이전 블록의 헤더를 보고 그 블록의 크기만큼 지금 블록의 사이즈에 추가함
        PUT(FTRP(bp), PACK(size, 0));               // 푸터에 먼저 조정하려는 크기로 상태 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 현재 헤더에서 앞블록의 헤더 위치로 이동한 다음, 조정한 size넣기
        bp = PREV_BLKP(bp);                         // bp를 그 앞블록의 헤더로 이동(늘리게 되면 이전블록의 헤더가 정식헤더가 되므로)
    }

    else{                                           // CASE 4 - 이전 블록과 다음 블록 모두 가용상태. 3개를 모두 통합해야함
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈 늘리기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    start_nextfit = bp;
    return bp;                                      // 4개 케이스중에 적용된거로 bp 리턴
}                                                   // 참고로 bp는 위에서 정했듯 항상 블록의 헤더 뒤에 위치하는게 좋기 때문에 연결이 끝나면 bp는 블록의 헤더에 위치해야 한다.




/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

 /* 데이터 할당 함수 만들기(malloc) 연결하는 함수도 있으니 가용 리스트에서 블록을 할당하는 함수를 만들어야함 */
void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char * bp;

    /* size 0 인 요청 무시 */
    if (size == 0) return NULL; // 인자로 받은 size가 0이니까 할당할 필요 없음

    /* overhead, 블록 사이즈 조정 */
    if (size <= DSIZE){
        asize = 2*DSIZE; // 헤더와 푸터를 포함해서 블록 사이즈를 다시 조정해야되니까 DSIZE의 2배를 준다.(헤더와 푸터 합쳐서 8바이트)헤더와 푸터에는 16/1 이 들어간다.
    }

    // 만약에 size가 10으로 들어왔다고 하자! 그럼 헤드와푸터를 포함해서 18바이트를 받아야하는데 16바이트로는 어림도 없음. 그럼 그 다음 8의 배수인 24바이트를 먹어야함
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // size가 8바이트보다 클때, 블록이 가질 수 있는 크기 중에 최적화된 크기로 재조정(오버헤드 바이트를 추가하고, 인접 8의 배수로 반올림), C에서 소숫점을 int로 반환할때 소숫점을 버리기 위해 쓰는 수식
    }

    /* fit에 맞는 가용 리스트 찾는다. */

    if ((bp = find_fit(asize))!= NULL){
        place(bp, asize);
        return bp; // place를 마친 블록의 위치를 리턴.
    }
    /* 위 과정에서 안됐다 = fit 맞는게 없다. 메모리를 더 가져와 block을 위치시킨다. */
    extendsize = MAX(asize, CHUNKSIZE); // asize와 chunksize(우리가 처음에 세팅한 사이즈) 중에 더 큰거로 넣는다.
    if ((bp =extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize); // 확장된 상태에서 asize 넣어라
    return bp;
}

/* find fit 구현해보자! */
static void *find_fit(size_t adjusted_size) {
    char *bp = start_nextfit;

    for (bp = start_nextfit; GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) { // 할당되지 않았고(가용이고) 사이즈가 
            return bp;
        }
    }
    return NULL;
}

/* place 함수를 구현해보자! */
static void place(void * bp, size_t asize){ // 들어갈 위치를 포인터로 받는다. (find fit에서 찾는 bp)
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1)); // 헤더에 size를 asize로 갱신 + 할당표시(1)
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);           // 다음블록의 블록포인터로 포인터 위치 변경
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 사용하고 남은 블록의 사이즈는 다 가용하다(0)는 것을 다음헤더에 저장
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1)); 
    }

}

//test

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // 어느 시점에 있는 bp를 인자로 받는다.
    size_t size = GET_SIZE(HDRP(bp)); // 얼만큼 free를 해야 하는지.
    PUT(HDRP(bp),PACK(size,0)); // header, footer 들을 free 시킨다. 안에 들어있는걸 지우는게 아니라 가용상태로 만들어버린다.
    PUT(FTRP(bp), PACK(size,0)); 
    coalesce(bp);
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
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














