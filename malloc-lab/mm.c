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


static char *heap_listp = NULL;  // 전역(정확히는 파일 내 전역) 변수로

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
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1 */
    if(prev_alloc && next_alloc)
    {
        return bp;
    }

    /* case 2 */
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
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
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

// 요청한 블록을 반환하고, 경계 태그 연결을 통해서 블록을 통합한다.
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 블록 사이즈를 저장

    PUT(HDRP(bp), PACK(size, 0)); // 헤더에 사이즈와 할당 안 함을 표시
    PUT(FTRP(bp), PACK(size, 0)); // 푸터에 사이즈와 할당 안 함을 표시
    coalesce(bp); // 인접 가용 블록들을 병합함.
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