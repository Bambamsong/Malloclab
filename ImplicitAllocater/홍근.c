/* Next fit */

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

// 각종 변수,함수 설정
#define WSIZE 4             // word and header footer 사이즈를 byte로.
#define DSIZE 8             // double word size를 byte로
#define CHUNKSIZE (1 << 12) // 2의 12승인 4096을 표시 페이지 사이즈인 4KB를 의미

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // x랑 y중 큰 값 반환

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산)
// size와 alloc을 받아서 하나의 워드로 패킹하는 역할을 함.
// size는 블록의 크기, alloc은 블록의 할당 여부를 나타내는 값임.
// ex size가 16이고 alloc이 1인 경우 PACK(16,1)은 이렇게 연산됨
//  00000000 00000000 00000000 00010000
//| 00000000 00000000 00000000 00000001
//  --------------------------------------
//  00000000 00000000 00000000 00010001
#define PACK(size, alloc) ((size) | (alloc))

/* address p위치에 words를 read와 write를 한다. */
// p주소 위치에 존재하는 주소값과 값(값에는 다른 블록의 주소를 담고있음)을 알 수 있다. 다른 블록을 가리켜야할때나 이동할때 사용된다.
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 블록의 주소를 담아둔다. 위치를 담아놔야 나중에 헤더나 푸터를 읽어서 이동 혹은 연결이 가능하다.

// address p위치로부터 size를 읽고 field를 할당
#define GET_SIZE(p) (GET(p) & ~0x7) // 비트 연산을 하게되면 ~0x7이기때문에 11111000이 된다. 이렇게 되면 뒤에 3자리를 제외한 값을 가져올 수 있음. 헤더에서 블록 size만 가져옴
#define GET_ALLOC(p) (GET(p) & 0x1) // 00000001 헤더에서 가용여부만 가져올것임.

/* given block ptr bp, 그것의 header와 footer의 주소를 계산*/
#define HDRP(bp) ((char *)(bp)-WSIZE)                        // bp가 어디에 있던지 상관없이 헤더 항상 WSIZE 앞에 위치한다.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp값에서 GET_SIZE(HDRP(bp))이정도를 가게 되면, 헤더와 풋터를 포함한 블록 전체값으로 가기 때문에 바로 다음 블록의 헤더까지 가게됨.
                                                             // 그렇기 때문에 풋터앞으로 가려면 다음 블록의 헤더,원래 블록의 풋터 총 8바이트 2블록을 이동해야 하므로 DSIZE를 빼야함
#define PREV_FOOTER(bp) ((char *)(bp)-DSIZE)

/* GIVEN block ptr bp, 이전 블록과 다음 블록의 주소를 계산*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // bp값에서 bp는 그대로 둔 상태에서 bp-WSIZE를 하게 되면 자신의 헤더 전과 이전블록 풋터의 중간 값으로 가게 되는데,
// 거기서 헤더를 읽어서 그만큼 앞으로 가면 다음 블록의 헤더 뒤에까지 갈 수 있게 된다.
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE))) // bp는 우선 그대로 둔 상태에서 bp-DSIZE를 하면 이전 블록의 풋터가 나오는데 그 값만큼 bp를 빼주면 전에 헤더 다음으로 갈 수 있다.

team_t team = {
    /* Team name */
    "duile",
    /* First member's full name */
    "Duile",
    /* First member's email address */
    "https://www.cnblogs.com/duile",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

static char *heap_listp;
static char *last_bp;

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(PREV_FOOTER(bp));     // 전 블록의 풋터 값에서 블록의 가용여부를 확인하기 위함
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 자기 블럭의 풋터와 다음 블럭의 헤더 사이에 위치함. 이걸 통해서 다음 블럭의 가용여부를 확인하려고 하는것임.
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블럭의 사이즈를 확인하기 위해서 bp-WSIZE를 진행해줌.

    if (prev_alloc && next_alloc)
    { // case 1 - 이전과 다음 블록이 모두 할당 되어있는 경우, 현재 블록의 상태는 할당에서 가용으로 변경
        // 이미 free에서 가용이 되어있어서 여기서는 free를 할 필요가 없음.
        last_bp = bp;
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {                                          // case2 - 이전 블록은 할당 상태, 다음 블록은 가용상태. 현재 블록은 다음 블록과 통합 됨.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더를 보고 그 블록의 크기만큼 지금 블록의 사이즈에 추가한다.
        PUT(HDRP(bp), PACK(size, 0));          // 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0));          // 푸터 갱신
    }
    else if (!prev_alloc && next_alloc)
    { // case 3 - 이전 블록은 가용상태, 다음 블록은 할당 상태. 이전 블록은 현재 블록과 통합.
        // 여기는 전에 이전에 위치해있는 free상태의 것을 합쳐야해서 우선 풋터부터 size만큼 갱신해주게 됨.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        // PREV_BLKP를 통해서 이전 블록의 풋터 뒤로 이동, 거기서 값을 읽어서 bp를 이전 블록의 헤더 뒤로 이동시킴, 거기서 HDRP를 통해서 헤더 앞으로 bp를 옮겨서 거기에 값을 갱신해둠.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // bp를 이전 블록의 헤더 다음으로 넣어둠.
        // 여기가 비어있기 때문.
        bp = PREV_BLKP(bp);
    }
    else
    {                                                                          // case 4- 이전 블록과 다음 블록 모두 가용상태. 이전,현재,다음 3개의 블록 모두 하나의 가용 블록으로 통합.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈 늘리기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                               // 이전 블록의 헤더값에 사이즈 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 다음 블록의 푸터값에 사이즈 갱신
        bp = PREV_BLKP(bp);                                                    // bp를 이전 블록으로 잡음.
    }
    last_bp = bp;
    return bp;
}
static void *extend_heap(size_t words)
{ // 새 가용 블록으로 힙 확장
    char *bp;
    size_t size; // size_t = unsigned int
    /* alignment 유지를 위해 짝수 개수의 words를 Allocate */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 홀수이면 +1은 한 값에 WSIZE곱셈, 짝수이면 그냥 그대로 곱셈진행
    //  홀수가 나오면 사이즈를 한 번 더 재정의. 힙에서 늘릴 사이즈를 재 정의
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        // sbrk를 통해서 추가 힙 메모리를 요청하는데 -1이 나온단거는 불가능하다는 얘기임
        //  bp의 사이즈를 long형으로 반환(사이즈를 늘려놓고 처리하려고)
        return NULL;
    } // 사이즈를 늘릴때마다 old brk는 과거 mem_brk위치로 감.

    /* free block 헤더와 푸터를 init하고 epilogue 헤더를 init*/
    PUT(HDRP(bp), PACK(size, 0));         // block의 헤더를 생성 /prologue block이 아닌 일반 블록 헤더를 생성. 현재 bp위치의 한칸 앞에 헤더를 생성
    PUT(FTRP(bp), PACK(size, 0));         // block의 풋터를 생성 /일반 블록의 풋터를 생성한다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 블록을 추가했으니 epilogue header의 위치를 새롭게 위치 조정해줌

    /* 만약 prev block이 free였다면, coalesce해라.*/
    return coalesce(bp); // 처음에는 coalesc를 할게 없지만 함수 재사용을 위해 리턴값으로 선언
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* create 초기 빈 heap*/
    // Q. 초기 빈 heap을 왜 16으로 진행하는가?
    // A. WISE는 word크기를 나타내는 매크로이며, 최소한의 블록 크기를 유지하기 위해 초기 빈 힙은 적어도 16바이트 이상의 크기를 가져야함.
    // 할당이 제대로 이루어지는지 확인하고, 할당이 실패한 경우에는 -1을 반환한다.
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                            // 초기 힙의 블록의 헤더, 0의 의미는 가용상태를 의미함
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 할당된 블록의 헤더를 설정, PACK(DSIZE,1)은 헤더를 패킹하는 매크로로 DSIZE는 더블워드(8바이트)를 나타내며 1은 할당 상태를 나타낸다.
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 세번째 워드에는 첫 번째 할당된 블록의 풋터를 설정함. 이 코드는 두번째 워드와 같은 값을 가지고 있음.
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 플록 헤더를 만듦. 뒤로 밀리는 형태이다.
    heap_listp += (2 * WSIZE);                     // 프롤로그블록의 중간 값을 가리키기 위해서 2*WSIZE값을 더해서 시작 위치를 변경해줌
    last_bp = heap_listp;

    // 이 함수를 호출하여 추가 메모리를 할당하고, 이 과정에서 초기 힙의 크기를 확장한다.
    // 첫번째 청크 사이즈를 할당하는 것
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

// 블록을 반환하고 경계 태그 연결 사용 -> 상수 시간 안에 인접한 가용 블록들과 통합하는 함수들
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 얼만큼 free해야 할 것 인가?
    PUT(HDRP(bp), PACK(size, 0));     // header, footer 들을 free 시킨다. 안에 내용을 지우는게 아니라 그냥 가용상태로만 만들어준다.
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *find_fit(size_t asize)
{ // first fit 검색을 수행
    void *bp;
    for (bp = last_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // heap_listp출발, 헤더의 크기만큼, 다음블록의 헤더 다음까지 for문을 진행하면서,
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 이 블록이 가용 가능한지 확인하고, 내가 갖고 있는 asize를 담을 수 있으면
        {
            // bp의 값을 리턴
            return bp;
        }
    }
    return NULL; // 종료 되면 null 리턴. no fit 상태.
}
// 들어갈 위치를 포인터로 받는다.(find fit에서 찾는 bp) 크기는 asize로 받음.
static void place(void *bp, size_t asize)
{                                       // 요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.
    size_t csize = GET_SIZE(HDRP(bp));  // 헤더에 접근해서 블록의 사이즈를 들고옴
    if ((csize - asize) >= (2 * DSIZE)) // 현재 블록 사이즈 안에서 asize를 넣은 이후에 2*DSIZE(헤더와,푸터, 그리고 데이터값)을 넣을 만큼 남냐?
    {                                   // 남으면 다른데이터를 넣을 수 있음
        // 헤더 위치에 asize만큼으로 바꾸고. 가용상태를 1로 바꿔준다.
        PUT(HDRP(bp), PACK(asize, 1));
        // 푸터 위치에 asize만큼으로 바꾸고.가용상태를 1로 바꿔준다.
        PUT(FTRP(bp), PACK(asize, 1));
        // bp를 다음 헤더의 뒤로 갱신시킴.
        bp = NEXT_BLKP(bp);
        // 그리고서 그 헤더에 가용 상태를 0으로 설정해주고 나머지 블록에 대해서 사용 가능하다라고 헤더와 풋터에 넣어줌
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        // 남은 가용 공간이 따로 없다는 것이니까 그냥 csize를 다 넣어줌
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    // last_bp = HDRP(bp);
} /* * mm_malloc - Allocate a block by incrementing the brk pointer.  *     Always allocate a block whose size is a multiple of the alignment.  */
void *mm_malloc(size_t size) // 가용 리스트에서 블록 할당 하기
{
    size_t asize;      // 블록 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp;

    /* 거짓된 요청 무시*/
    if (size == 0)
        return NULL;

    /* overhead, alignment 요청 포함해서 블록 사이즈 조정*/
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE; // 헤더와 푸터를 포함해서 블록 사이즈를 다시 조정해야되니까 DSIZE의 2배를 준다.(헤더와 푸터 합쳐서 8바이트)예를 들어 헤더와 푸터에는 16/1 이 들어간다.
        // 사이즈가 8보다 작다는 것은 헤더+푸터 8바이트에서 size가 아무리 커도 8이기 때문에 max값은 16이 나온다. 따라서 asize를 16으로 설정하는 것임.
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
        // ex) size = 10이라면
        // asize= 8*((4+8+7)/8) => 16이됨
        // ex) 30일때
        // asize = 8* ( (30+8+7)/8 ) =>40이됨.
        // size보다 클 때, 블록이 가질 수 있는 크기 중에 최적화된 크기로 재조정.
        // 이 코드 자체가 인접한 8의 배수를 만들어주는 코드임
    }
    /* fit에 맞는 free 리스트를 찾는다.*/
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    /* fit 맞는게 없다. 메모리를 더 가져와 block을 위치시킨다.*/
    extendsize = MAX(asize, CHUNKSIZE); // asize와 CHUNKSIZE중에 더 큰 값으로 확장시킴.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    // 필요하면 기존 블록을 분할한다. → 맞는 블록을 찾지 못하면 힙을 늘리고 다시 배치한다.
    place(bp, asize); // 확장 상태에서 bp에 asize를 넣어라 라는 의미
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */

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