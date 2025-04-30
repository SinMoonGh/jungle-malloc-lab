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

/* 힙 검사기 */
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "3 team",
    /* First member's full name */
    "Myeong Hoon",
    /* First member's email address */
    "jungle@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};


/* 아래 ALIGH(size) 함수에서 할당할 크기인 size를 8의 배수로 맞춰서 할당하기 위한 매크로 */
#define ALIGNMENT 16

/* 할당할 크기인 size를 보고 8의 배수 크기로 할당하기 위해 size를 다시 align하는 작업을 한다. 만약 size가 4이면 (4+8-1) = 11 = 0000 1011 이고
이를 ~0xF = 1111 1000과 AND 연한하면 0000 1000 = 8이 되어 적당한 16의 배수 크기로 align할 수 있다.*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* 메모리 할당 시 기본적으로 header와 footer를 위해 필요한 더블워드만큼의 메모리 크기.
    long형인 size_t의 크기만큼 8을 나타내는 매크로.
 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 8 // 헤더와 푸터의 사이즈를 4byte로 잡은 것 같은데 맥은 4바이트가 아닐 수도 있다. 만약 64비트 환경이라면 8바이트로 변경해줘야 함.
#define DSIZE 16 // 더블 워드 사이즈. 블록 하나의 최소 바이트를 말한다.
#define CHUNKSIZE (1<<12) // 왼쪽으로 12비트 이동. 그러면 2의 12승임. 2의 12승은 = 4096(바이트)이고, 4096바이트는 4KB가 된다. 초기에 malloc을 생성하면 공간이 없기 때문에 먼저 chunksize만큼 요청한다. 또한 가용 블록이 더이상 존재하지 않을 때 호출한다.
#define MINIMUM 32 // header, footer, pred, succ 각각 1워드라서 최소 단위를 나타냄

#define MAX(x, y) ((x) > (y)? (x):(y)) // x와 y 중 큰 값을 리턴한다.

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합하여 헤더와 풋터에 저장할 수 있는 값을 리턴한다.

#define GET(p) (*(unsigned long *)(p)) // p가 참조하는 워드를 읽어서 반환한다. p는 void형 포인터라서 역참조는 할 수 없다?
#define PUT(p, val) (*(unsigned long *)(p) = (val)) // p가 가리키는 워드에 val을 저장하는 역할을 하는데 이때 블록의 크기와 가용 비트를 저장한다.
#define PUT_PTR(p, val) (*(void **)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7) // p가 가리키는 헤더와 풋터에 사이즈를 저장
#define GET_ALLOC(p) (GET(p) & 0x1) // p가 가리키는 헤더와 풋터에 할당 비트를 저장한다.

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록 포인터 bp가 주어졌을 때 헤더를 가리키는 포인터를 리턴한다. 주소가 아니고?
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 포인터 bp가 주어졌을 때 풋터를 가리키는 포인터를 리턴한다.

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록 포인터를 리턴한다.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록 포인터를 리턴한다.

/* explicit free List */
#define GET_PRED(bp) (*(void **)(bp)) // pred 포인터를 읽어옴
#define GET_SUCC(bp) (*(void **)((char *)bp + WSIZE)) // succ 포인터를 읽어옴
/* explicit free List End */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);       // first fit으로 적절한 가용 블록 리턴
static void place(void *bp, size_t asize); // 남은 블록 분할
static void insert_in_head(void *ptr); // free 리스트의 head부분에 삽입
static void remove_block(void *ptr); // free 리스트의 해당 블럭을 삭제

static void *heap_listp = NULL;  // 전역(정확히는 파일 내 전역) 변수로
static void *free_listp = NULL; // free list의 시작 주소를 저장할 변수

/* mm_malloc이나 mm_free를 호출하기 전에 mm_init 함수를 호출해서 힙을 초기화해줘야 한다 */
int mm_init(void)
{
    // 메모리 시스템에서 6워드를 가져와서 빈 가용리스트를 만들 수 있도록 초기화 
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
    {
        return -1;
    }
    
    PUT(heap_listp, 0); // 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + (3*WSIZE), PACK(2*DSIZE, 0)); // dummy free block 헤더
    PUT(heap_listp + (4*WSIZE), NULL);           // dummy block pred
    PUT(heap_listp + (5*WSIZE), NULL);           // dummy block succ
    PUT(heap_listp + (6*WSIZE), PACK(2*DSIZE, 0)); // dummy block 푸터
    PUT(heap_listp + (7*WSIZE), PACK(0, 1)); // 에필로그 헤더
    heap_listp += (4*WSIZE);

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
    // mm_check();
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

/* 병합 함수 */
static void *coalesce(void *bp)
{
    // mm_check();
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 푸터에 저장된 size, alloc의 정보를 추출한 후 alloc의 정보만 저장한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에 저장된 size, alloc의 정보를 추출한 후 alloc의 정보만 저장한다.
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 헤더에서 size의 정보를 추출해서 저장한다.

    /* case 1. 이전 블록과 다음 블록이 모두 할당되어 있다면 병합하지 않고,free 리스트의 앞쪽에 삽입해 준다. */
   if (prev_alloc && next_alloc) {
       insert_in_head(bp);
       return bp;
   }

    /* case 2 */
    else if (prev_alloc && !next_alloc) // 이전 블록은 할당되어 있지만 다음 블록은 가용 상태일 때
    {
        remove_block(NEXT_BLKP(bp)); // 현재 블럭이랑 병합하기 위해 next 블럭을 free 리스트에서 제거함.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록의 크기와 다음 블록의 크기를 더한다.
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 헤더에 블록 크기와 가용 여부를 저장한다.
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 푸터에 블록 크기와 가용 여부를 저장한다. 현재 푸터에 블록의 크기를 변경했으므로 16바이트만큼 이동하기 때문에 현재 푸터에 저장하는 것이 맞다.   
    }

    /* case 3 */
    else if (!prev_alloc && next_alloc) // 이전 블록이 가용 상태이고, 다음 블록은 할당 상태이다.
    {
        remove_block(PREV_BLKP(bp)); // 현재 블럭이랑 병합하기 위해 prev 블럭을 free 리스트에서 제거함.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 현재 블록의 크기와 이전 블록의 크기를 합한다.
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 푸터에 블록의 크기와 가용 여부를 저장한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 블록의 크기와 가용 여부를 저장한다.
        bp = PREV_BLKP(bp);
    }

    else // 이전 블록도 가용 상태이고 다음 블록도 가용 상태일 때
    {
        remove_block(PREV_BLKP(bp)); // 현재 블럭이랑 병합하기 위해 prev 블럭을 free 리스트에서 제거함.
        remove_block(NEXT_BLKP(bp)); // 현재 블럭이랑 병합하기 위해 next 블럭을 free 리스트에서 제거함.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록의 크기와 현재 블록의 크기 다음 블록의 크기까지 다 합한다.
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 블록의 크기와 가용 여부 정보를 저장한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 다음 블록의 푸터에 블록의 크기와 가용 여부 정보를 저장한다.
        bp = PREV_BLKP(bp);
    }

    insert_in_head(bp); // 병합된 새로운 블럭을 다시 free 리스트에 삽입
        
    return bp;
}

/* size 바이트의 메모리 블록을 요청한다.
추가적인 요청들을 체크한 후 할당기는 요청한 블록 크기를 조절해서 헤더와 풋터를 위한 공간을 확보하고,
더블 워드 요건을 만족시킨다. */
void *mm_malloc(size_t size) // 사용자가 요청한 데이터의 크기
{
    // mm_check();
    size_t asize; // 헤더와 푸터를 더한 최소 크기의 블록
    size_t extendsize; // 확장된 블록 크기
    char *bp; // 현재 블록 위치

    if (size == 0) // 사용자가 요청한 데이터의 크기가 0이라면
    {
        return NULL; // 확장 안함
    }

    if (size <= DSIZE) // 블록의 크기가 더블 워드 크기라면
    {
        asize = 2*DSIZE; // 더블 워드 8이고, 요청된 데이터가 8보다 작으므로 8을 더해줘서 16바이트짜리 블록을 만들어 준다.
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
    // mm_check();
    size_t size = GET_SIZE(HDRP(bp)); // 블록 사이즈를 저장

    PUT(HDRP(bp), PACK(size, 0)); // 헤더에 사이즈와 할당 안 함을 표시
    PUT(FTRP(bp), PACK(size, 0)); // 푸터에 사이즈와 할당 안 함을 표시
    coalesce(bp); // 인접 가용 블록들을 병합함.
}

/* first fit으로 구현 */
static void *find_fit(size_t asize)
{
    // mm_check();
    void *bp = free_listp; // 현재 위치 포인터

    while (bp != NULL) {
       if (GET_SIZE(HDRP(bp)) >= asize) {
           return bp;
       }
       bp = GET_SUCC(bp);
    }
    return NULL; // 없으면 NULL을 반환
}

/* 요청한 블록을 새 가용 블록에 배치하고, 필요한 경우에 블록을 분할한다. */
static void place(void* bp, size_t asize)
{
    // mm_check();
    size_t csize = GET_SIZE(HDRP(bp)); // 새 가용 블록의 크기


    if ((csize - asize) >= (2*DSIZE)) // 새 가용 블럭의 크기가 요청된 데이터를 할당하고도 남은 공간이 2워드 이상이라면 - 사실상 가용 블럭 분할하겠다는 거임
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 헤더에 요청한 데이터의 크기와 할당 비트를 저장
        PUT(FTRP(bp), PACK(asize, 1)); // 푸터에 요청한 데이터의 크기와 할당 비트를 저장
        remove_block(bp); // 할당된 블럭은 free 리스트에서 제거

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 헤더에 요청된 데이터를 저장하고 남은 블럭의 크기와 할당 비트를 저장
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 푸터에 요청된 데이터를 저장하고 남은 블럭의 크기와 할당 비트를 저장
        insert_in_head(bp); // 저장하고 남은 블럭을 free 리스트에 삽입
    }
    else // 할당하고 남은 공간이 2워드가 되지 않는다면 분할하지 않는다
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 헤더에 새 가용 블록의 크기와 할당 비트 저장
        PUT(FTRP(bp), PACK(csize, 1)); // 푸터에 새 가용 블록의 크기와 할당 비트 저장
        remove_block(bp); // 할당된 블럭은 free 리스트에서 제거
    }
}

/*
기존의 할당된 메모리 블록의 크기를 변경하고, 그에 맞는 새로운 주소를 반환한다
 */
void *mm_realloc(void *ptr, size_t size) {
   if (ptr == NULL)
       return mm_malloc(size);
   if (size == 0) {
       mm_free(ptr);
       return NULL;
   }

   size_t old_block = GET_SIZE(HDRP(ptr));
   size_t old_payload = old_block - 2 * WSIZE;
   size_t new_asize;

   if (size <= DSIZE) {
       new_asize = 2 * DSIZE;
   } else {
       new_asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
   }

   // 1. in-place 축소
   if (new_asize <= old_block) {
       if (old_block - new_asize >= 2 * DSIZE) {
           PUT(HDRP(ptr), PACK(new_asize, 1));
           PUT(FTRP(ptr), PACK(new_asize, 1));
           void *nbp = NEXT_BLKP(ptr);
           size_t remain = old_block - new_asize;
           PUT(HDRP(nbp), PACK(remain, 0));
           PUT(FTRP(nbp), PACK(remain, 0));
           insert_in_head(nbp);
       }
       return ptr;
   }

   // 2. in-place 확장
   if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) {
       size_t nsize = old_block + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
       if (nsize >= new_asize) {
           remove_block(NEXT_BLKP(ptr));
           PUT(HDRP(ptr), PACK(nsize, 1));
           PUT(FTRP(ptr), PACK(nsize, 1));
           return ptr;
       }
   }

   // 3. 새로 malloc -> 데이터 복사
   void *new_ptr = mm_malloc(size);
   if (new_ptr == NULL)
       return NULL;

   size_t copy = (old_payload < size) ? old_payload : size;
   memcpy(new_ptr, ptr, copy);
   mm_free(ptr);
   return new_ptr;
}

/* 가용 블럭을 free 리스트 맨 앞에 삽입 */
static void insert_in_head(void *bp)
{
    // mm_check();
    GET_SUCC(bp) = free_listp;
    GET_PRED(bp)= NULL;
     // 새로 삽입된 블럭의 succ 포인터가 head(free_listp = heap_listp + 2*WSIZE;)를 가리키게 함 
    if (free_listp != NULL)
    {
        GET_PRED(free_listp) = bp; // root의 pred 포인터를 현재 블럭을 가리키게 함
    }
    free_listp = bp; // head(free_listp = heap_listp + 2*WSIZE;) 포인터가 현재 블럭을 가리키게 이동시킨다.
}

/* 할당 상태로 바뀐 블럭은 free 리스트에서 삭제 */
static void remove_block(void *bp) {
   // bp 블록의 이전 블록(pred)
   void *pred = GET_PRED(bp);
   // bp 블록의 다음 블록(succ)
   void *succ = GET_SUCC(bp);

   // bp 앞에 다른 블록(pred)이 있는 경우
   if (pred != NULL)
       // pred 블록의 successor를 bp의 successor로 연결
       GET_SUCC(pred) = succ;
   else
       // bp가 free list의 맨 앞이라면 첫 블록 주소를 bp 블록의 다음 블록으로 변경
       free_listp = succ;

   // bp 뒤에 다른 블록(succ)이 있는 경우
   if (succ != NULL)
       // succ 블록의 predecessor를 bp의 predecessor로 연결
       GET_PRED(succ) = pred;
}