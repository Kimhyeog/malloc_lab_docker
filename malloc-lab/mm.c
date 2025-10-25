/*
 * mm-implicit.c - implicit free list 기반 malloc 구현
 *
 * 각 블록은 다음 형태로 구성됩니다.
 *  -----------------------------------------------------
 *  | header | payload ... | footer |
 *  -----------------------------------------------------
 *  header, footer : 블록 전체 크기 + 할당 여부 비트
 *
 *  기본 동작:
 *    - mm_init: 초기 힙(prologue, epilogue) 생성 및 확장
 *    - mm_malloc: first-fit으로 free 블록 탐색 후 배치
 *    - mm_free: free 표시 후 인접 free 블록 coalesce
 *    - mm_realloc: malloc+copy+free 단순 구현
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Word and header/footer size (bytes) */
#define WSIZE 4

/* Double word size (bytes) */
#define DSIZE 8

/* Extend heap by this amount (bytes) */
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// header/footer pack: size + alloc bit
#define PACK(size, alloc) ((size) | (alloc))

// 메모리 주소 p에 값 val 쓰기
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// header/footer 읽기
#define GET(p) (*(unsigned int *)(p))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*
 * 블록 포인터 bp가 주어지면 해당 블록의 header를 가리키는 포인터를 리턴
 * 🤔 왜 (char *)로 형 변환을 할까?
 * => 포인터 연산을 바이트 단위로 정확하게 하기 위해 1바이트인 char 타입의 포인터로 변환한다.
 */
#define HDRP(bp) ((char *)(bp) - WSIZE)

/* 블록 포인터 bp가 주어지면 해당 블록의 footer를 가리키는 포인터를 리턴 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*
 * 다음 블록의 포인터를 리턴하는 함수
 * GET_SIZE(((char *)(bp)-WSIZE))는 현재 블록의 헤더에 있는 사이즈 정보를 읽어옴
 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))

/*
 * 이전 블록의 포인터를 리턴하는 함수
 * GET_SIZE((char *)(bp)-DSIZE)는 이전 블록의 footer에 있는 사이즈 정보를 읽어옴
 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

////////////////////////////////////////////////////////////////////////////////////////////////////////

/* 힙의 시작 지점을 가리키는 포인터 */
static void *heap_listp;

/* 힙 메모리 영역 확장하기 */
static void *extend_heap(size_t words);

/* 가용 블록 연결하기 */
static void *coalesce(void *bp);

/* 가용한 블록 검색하기 (first-fit) */
static void *find_fit(size_t asize);

/* 할당된 블록 배치하기 */
static void place(void *bp, size_t asize);

// static void *next_fit(size_t asize); // mm_malloc 위쪽에 추가
// static char *last_bp;                // static 전역변수
////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 힙 초기화하기 (시스템 호출이 실패하면 -1을 반환함)
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    // Alignment padding (힙의 시작주소에 0 할당)
    PUT(heap_listp, 0);

    // Prologue header & footer
    // Prologue 블록은 헤더와 푸터로만 구성된 8바이트(= Double word size) 할당 블록임
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));

    // Epilogue header
    // 에필로그 블록은 헤더만으로 구성된 사이즈가 0인 블록. 항상 할당된 상태로 표시됨
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);

    // CHUCKSIZE / WSIZE (= 2^12 / 4 = 1024) 바이트만큼 힙 확장시키기
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* 힙 영역 확장하기 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 정렬을 유지하기 위해 짝수 사이즈의 words를 할당
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // free 상태 블록의 헤더와 푸터를 초기화하고 새로운 에필로그 헤더를 초기화
    PUT(HDRP(bp), PACK(size, 0));         // Free block header
    PUT(FTRP(bp), PACK(size, 0));         // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header

    // 만약 이전 블록이 free 상태라면 연결(coalesce)
    return coalesce(bp);
}

/* 가용 블록 연결하기 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                   // 해제된 현재 블록의 사이즈

    // Case 1. 이전 블록, 다음 블록 모두 할당된 상태
    if (prev_alloc && next_alloc)
    {
        return bp; // => 아무 작업 없이 현재 블록 포인터 리턴
    }

    // Case 2. 이전 블록은 할당된 상태, 다음 블록은 가용한 상태
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록의 사이즈 + 다음 블록 사이즈
        PUT(HDRP(bp), PACK(size, 0));          // 헤더 사이즈 수정
        PUT(FTRP(bp), PACK(size, 0));          // 푸터 사이즈 수정
    }

    // Case 3. 이전 블록은 가용한 상태, 다음 불록은 할당된 상태
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 가용 블록이 이전 블록부터 시작해야 하므로 이전 블록 헤더의 사이즈를 수정
        bp = PREV_BLKP(bp);
    }

    // Case 4. 이전 블록, 다음 블록 모두 가용한 상태
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // last_alloc = bp;

    return bp;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

// static void *next_fit(size_t asize)
// {
//     char *bp = last_bp;
//     for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
//         {
//             last_bp = bp;
//             return bp;
//         }
//     }
//     for (bp = heap_listp; bp != last_bp; bp = NEXT_BLKP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
//         {
//             last_bp = bp;
//             return bp;
//         }
//     }
//     return NULL;
// }

void *mm_malloc(size_t size)
{
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit
    char *bp;

    // 유효하지 않은 요청인 경우 NULL 리턴
    if (size == 0)
        return NULL;

    // overhead 추가와 정렬요건을 충족을 위해 블록사이즈 조정
    // overhead란 시스템이 특정 작업을 수행하는 데 필요한 추가적인 리소스나 시간을 가리키는 용어로 여기에서는 헤더와 푸터를 의미
    if (size <= DSIZE)
        asize = 2 * DSIZE; // 더블 워드 정렬 조건을 충족하기 위해
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // size에 가장 가까운 double word size의 배수 찾기

    // 가용한 블록 찾기
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 만약 가용한 블록이 없는 경우 힙 메모리 영역을 확장하고 블록을 배치
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    char *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp; // 조건 맞으면 그 블록 반환
    }

    return NULL; // 찾는 블록 없으면 NULL
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        // 블록 분할
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        // 블록 전체 사용
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_free - 메모리 반환하기
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    // 헤더와 푸터의 할당 비트를 0으로 수정하여 해제
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
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