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
    ""};


#define WSIZE 4 // 헤더와 푸터의 사이즈를 4byte로 잡은 것 같은데 맥은 4바이트가 아닐 수도 있다. 만약 64비트 환경이라면 8바이트로 변경해줘야 함.
#define DSIZE 8 // 더블 워드 사이즈. 블록 하나의 최소 바이트를 말한다.
#define CHUNKSIZE (1<<12) // 왼쪽으로 12비트 이동. 그러면 2의 12승임. 2의 12승은 = 4096(바이트)이고, 4096바이트는 4KB가 된다. 초기에 malloc을 생성하면 공간이 없기 때문에 먼저 chunksize만큼 요청한다. 또한 가용 블록이 더이상 존재하지 않을 때 호출한다.

#define MAX(x, y) ((x) > (y)? (x):(y)) // x와 y 중 큰 값을 리턴한다.

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합하여 헤더와 풋터에 저장할 수 있는 값을 리턴한다.

#define GET(p) (*(unsigned int *)(p)) // p가 참조하는 워드를 읽어서 반환한다. p는 void형 포인터라서 역참조는 할 수 없다?
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 워드에 val을 저장하는 역할을 하는데 이때 블록의 크기와 가용 비트를 저장한다.

#define GET_SIZE(p) (GET(p) & ~0x7) // p가 가리키는 헤더와 풋터에 사이즈를 저장
#define GET_ALLOC(p) (GET(p) & 0x1) // p가 가리키는 헤더와 풋터에 할당 비트를 저장한다.

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록 포인터 bp가 주어졌을 때 헤더를 가리키는 포인터를 리턴한다. 주소가 아니고?
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 포인터 bp가 주어졌을 때 풋터를 가리키는 포인터를 리턴한다.

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록 포인터를 리턴한다.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록 포인터를 리턴한다.

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);       // first fit으로 적절한 가용 블록 리턴
static void place(void *bp, size_t asize); // 남은 블록 분할
static char *heap_listp = NULL;  // 전역(정확히는 파일 내 전역) 변수로
static char *next_fitp = NULL;

/* mm_malloc이나 mm_free를 호출하기 전에 mm_init 함수를 호출해서 힙을 초기화해줘야 한다 */
int mm_init(void)
{
    // 메모리 시스템에서 4워드를 가져와서 빈 가용리스트를 만들 수 있도록 초기화
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }
    
    PUT(heap_listp, 0); // 패딩 블록이다. 블록 크기가 0이고, 가용/할당 상태도 0
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더 size 1워드에 alloc 1
    PUT(heap_listp  + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터 size 2워드에 alloc 1
    PUT(heap_listp  + (3*WSIZE), PACK(0, 1)); // 에필로그 헤더 사이즈 0에 alloc 1
    heap_listp += (2*WSIZE); // heap_listp가 16번지(프롤로그 블록의 payload 위치)로 이동

    /* 힙을 chunksize 바이트로 확장하고, 초기 가용 블록을 생성한다. */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

/* 힙이 초기화 될 때와 mm_malloc이 적당한 fit을 찾지 못했을 때 호출되는 함수. 
이전 힙이 가용 블록으로 끝났다면 두 개의 가용 블록을 통합하기 위해 coalesce 함수를 호출하고, 
통합된 블록의 블록 포인터를 리턴한다 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 정렬을 유지하기 위해서 요청한 크기를 인접 2워드의 배수(8바이트)로 반올림하며 그 후 메모리 시스템으로부터 추가적인 힙 공간을 요청한다.
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    /* 새 가용 블록의 헤더 푸터 생성 및 에필로그 헤더 초기화 */
    PUT(HDRP(bp), PACK(size, 0)); // 새 가용 블록의 헤더
    PUT(FTRP(bp), PACK(size, 0)); // 새 가용 블록의 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 이 블록의 마지막 워드는 새 에필로그 블록 헤더가 된다.

    /* 이전 힙이 가용 블록으로 끝났다면 두 개의 가용 블록을 통합하기 위해 coalesce 함수를 호출하고, 통합된 블록의 블록 포인터를 리턴한다 */
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 푸터에 저장된 size, alloc의 정보를 추출한 후 alloc의 정보만 저장한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에 저장된 size, alloc의 정보를 추출한 후 alloc의 정보만 저장한다.
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 헤더에서 size의 정보를 추출해서 저장한다.

    /* case 1 */
    if(prev_alloc && next_alloc) // 이전 블록과 다음 블록이 모두 할당되어 있다면 병합하지 않고, 그대로 bp를 반환한다.
    {
        return bp;
    }

    /* case 2 */
    else if (prev_alloc && !next_alloc) // 이전 블록은 할당되어 있지만 다음 블록은 가용 상태일 때
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록의 크기와 다음 블록의 크기를 더한다.
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 헤더에 블록 크기와 가용 여부를 저장한다.
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 푸터에 블록 크기와 가용 여부를 저장한다. 현재 푸터에 블록의 크기를 변경했으므로 16바이트만큼 이동하기 때문에 현재 푸터에 저장하는 것이 맞다.   
    }

    /* case 3 */
    else if (!prev_alloc && next_alloc) // 이전 블록이 가용 상태이고, 다음 블록은 할당 상태이다.
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 현재 블록의 크기와 이전 블록의 크기를 합한다.
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 푸터에 블록의 크기와 가용 여부를 저장한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 블록의 크기와 가용 여부를 저장한다.
        bp = PREV_BLKP(bp); // 현재 블록을 가리키는 포인터를 이전 블록으로 이동시킨다.
    }

    else // 이전 블록도 가용 상태이고 다음 블록도 가용 상태일 때
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록의 크기와 현재 블록의 크기 다음 블록의 크기까지 다 합한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 블록의 크기와 가용 여부 정보를 저장한다.
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 푸터에 블록의 크기와 가용 여부 정보를 저장한다.
        bp = PREV_BLKP(bp); // 현재 블록 위치 포인터를 이전 블록으로 이동시킨다.
    }

    next_fitp = bp; // 여기서 많이 헷깔렸는데 병합한 뒤에 해당 블록에 next fit 포인터를 이동시키는 이유는 인접한 블록을 next fit이 가리키고 있을 경우 가리키고 있는 블록이 병합이 되버리면 next fit 포인터는 잘못된 주소를 가리킬 수 있다.
    return bp;
}

/* size 바이트의 메모리 블록을 요청한다.
추가적인 요청들을 체크한 후 할당기는 요청한 블록 크기를 조절해서 헤더와 풋터를 위한 공간을 확보하고,
더블 워드 요건을 만족시킨다. */
void *mm_malloc(size_t size) // 사용자가 요청한 데이터의 크기
{
    size_t asize; // 헤더와 푸터를 더한 최소 크기의 블록
    size_t extendsize; // 확장된 블록 크기
    char *bp; // 현재 블록 위치

    if (size == 0) // 사용자가 요청한 데이터의 크기가 0이라면
    {
        return NULL; // 확장 안함
    }

    if (size <= DSIZE) // 블록의 크기가 더블 워드 크기라면
    {
        asize = 2*DSIZE; // 더블 워드 16이고, 요청된 데이터가 16보다 작으므로 16을 더해줘서 32바이트짜리 블록을 만들어 준다.
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 일반적인 규칙은 오버헤드 바이트를 추가하고, 인접 8의 배수로 반올림 한다.
    }

    if ((bp = find_fit(asize)) != NULL) // 할당기가 요청한 크기를 조정한 후에 적절한 가용 블록을 가용 리스트에서 검색한다.
    {
        place(bp, asize); // 만일 맞는 블록을 찾으면 할당기는 요청한 블록을 배치하고, 옵션으로 초과 부분을 분할하고, 새롭게 할당한 블록을 반환한다.
        return bp; 
    }

    extendsize = MAX(asize, CHUNKSIZE); // 4KB 확장
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 만일 할당기가 맞는 블록을 찾지 못하면 힙을 새로운 가용 블록으로 확장한다.
    {
        return NULL;
    }
    place(bp, asize); // 요청한 블록을 이 새 가용 블록에 배치하고, 필요한 경우에 블록을 분할한다.

    return bp; // 새롭게 할당한 블록의 포인터를 반환한다.
}

// 요청한 블록을 반환하고, 경계 태그 연결을 통해서 블록을 통합한다.
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 블록 사이즈를 저장

    PUT(HDRP(bp), PACK(size, 0)); // 헤더에 사이즈와 할당 안 함을 표시
    PUT(FTRP(bp), PACK(size, 0)); // 푸터에 사이즈와 할당 안 함을 표시
    coalesce(bp); // 인접 가용 블록들을 병합함.
}

/* next fit으로 구현 */
static void *find_fit(size_t asize)
{
    void *bp; // 현재 블록 주소
    
    if(next_fitp == NULL) // 할당되거나 병합된 블록이 없다면
    {
        next_fitp = heap_listp; // 처음부터 탐색
    }

    for (bp = next_fitp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // GET_SIZE(HDRP(bp))가 0인 경우는 에필로그 블록 밖에 없음. 따라서 이전 블록부터 힙 전체를 순회하겠다는 코드
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용 블록이면서 요청된 크기보다 블록의 크기가 더 클 경우
        {
            return bp; // 블록의 위치 반환
        }
    }

    for (bp = heap_listp; bp < next_fitp; bp = NEXT_BLKP(bp)) // 만약 가용 블럭을 찾지 못한다면 힙 시작부터 next fit 전까지 순회한다
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용 블록이면서 요청된 크기보다 블록의 크기가 더 클 경우 
        {
            return bp; // 블록의 위치 반환
        }
    }

    return NULL; // 아니면 해당 블록이 없음을 반환
}

/* 요청한 블록을 새 가용 블록에 배치하고, 필요한 경우에 블록을 분할한다. */
static void place(void* bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 새 가용 블록의 크기

    if ((csize - asize) >= (2*DSIZE)) // 새 가용 블럭의 크기가 요청된 데이터를 할당하고도 남은 공간이 2워드 이상이라면 - 사실상 가용 블럭 분할하겠다는 거임
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 헤더에 요청한 데이터의 크기와 할당 비트를 저장
        PUT(FTRP(bp), PACK(asize, 1)); // 푸터에 요청한 데이터의 크기와 할당 비트를 저장
        bp = NEXT_BLKP(bp); // 다음 블럭으로 이동
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 헤더에 요청된 데이터를 저장하고 남은 블럭의 크기와 할당 비트를 저장
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 푸터에 요청된 데이터를 저장하고 남은 블럭의 크기와 할당 비트를 저장
    }
    else // 할당하고 남은 공간이 2워드가 되지 않는다면 분할하지 않는다
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 헤더에 새 가용 블록의 크기와 할당 비트 저장
        PUT(FTRP(bp), PACK(csize, 1)); // 푸터에 새 가용 블록의 크기와 할당 비트 저장
    }

    next_fitp = bp; // next fit은 처음부터 가용 공간을 찾는 것이 아니라 할당된 블록의 위치부터 가용 공간을 탐색한다.
}

/*
기존의 할당된 메모리 블록의 크기를 변경하고, 그에 맞는 새로운 주소를 반환한다
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldbp = bp; // 기존의 블록 포인터
    void *newbp; // 새로운 블록 포인터
    size_t copySize; // 블록 크기를 복사해서 저장할 변수

    if (size <= 0) // 요청한 데이터의 크기가 0보다 작다면
    {
        mm_free(bp); // 기존의 블록을 해제시킨다.
        return 0;
    }

    newbp = mm_malloc(size); // size 크기의 메모리 블록을 할당하고 그 포인터를 반환한다.
    if (newbp == NULL) // 새로운 메모리 할당 실패
        return NULL;

    copySize = *(size_t *)((char *)oldbp - SIZE_T_SIZE); // 기존 블록의 크기를 복사한다
    if (size < copySize) // 기존 블록의 크기가 작을 경우 
        copySize = size; // 기존 블록의 크기를 복사한다.
    memcpy(newbp, oldbp, copySize); // 기존 블록의 크기를 복사해서 새로운 블록을 생성할 때 사용한다.
    mm_free(oldbp); // 기존 블록은 해제
    return newbp; // 새롭게 생성된 블록의 포인터를 반환한다
}