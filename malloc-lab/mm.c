/*
 * mm-segregated.c - Segregated explicit free lists (best-fit) 기반 malloc 구현
 *
 * --- 변경된 구조 ---
 *
 * [할당된 블록]
 * -----------------------------------------------------
 * | header (4B) | payload ... | footer (4B) |
 * -----------------------------------------------------
 *
 * [비어있는 블록 (최소 24B)]
 * -----------------------------------------------------------------
 * | header (4B) | prev_ptr (8B) | next_ptr (8B) | ... | footer (4B) |
 * -----------------------------------------------------------------
 *
 * --- 핵심 로직 (Segregated Best-Fit) ---
 * - 힙은 여러 개의 '크기 클래스(Size Class)'로 나뉜 빈 블록 리스트를 가짐
 * - mm_init: 크기 클래스 리스트(seg_list_roots)를 NULL로 초기화
 * - mm_malloc:
 * 1. 요청 크기(asize)에 맞는 크기 클래스 리스트를 찾음
 * 2. 해당 리스트부터 더 큰 리스트까지 탐색하며 (Best-Fit)
 * 3. 요청 크기(asize)와 가장 차이가 적은(가장 딱 맞는) 블록을 선택
 * - place:
 * 1. 선택된 블록을 리스트에서 제거
 * 2. 블록 분할(split)이 발생하면, 남은 블록을 알맞은 리스트에 삽입
 * - mm_free:
 * 1. 블록을 'free' 표시
 * 2. coalesce를 호출해 인접 블록과 병합 (이때 인접 블록은 리스트에서 제거됨)
 * 3. 병합된 최종 블록을 알맞은 크기 클래스 리스트에 삽입
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
    "ateam (segregated-fit)",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* --- 기본 상수 및 매크로 (일부 변경) --- */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) /* 4096 bytes */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/* --- NEW: Segregated List를 위한 매크로 및 상수 --- */
#define GET_PREV_FREE(bp) (*(void **)(bp))
#define SET_PREV_FREE(bp, ptr) (*(void **)(bp) = (ptr))
#define GET_NEXT_FREE(bp) (*(void **)((char *)(bp) + DSIZE))
#define SET_NEXT_FREE(bp, ptr) (*(void **)((char *)(bp) + DSIZE) = (ptr))

#define NUM_CLASSES 10
/* --- NEW --- */
/* --- 추가 매크로 --- */
#define MIN_BLOCK_SIZE (3 * DSIZE) // 최소 블록 크기 (24바이트) 명시
////////////////////////////////////////////////////////////////////////////////////////////////////////
/* --- 전역 변수 --- */
static char *heap_listp = 0;
static void *seg_list_roots[NUM_CLASSES];

/* --- 함수 프로토타입 --- */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int get_class_index(size_t size);
static void insert_into_list(void *bp);
static void remove_from_list(void *bp);

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * get_class_index - 크기에 맞는 리스트 인덱스 반환
 */
static int get_class_index(size_t size)
{
    // Class 0: 24-31
    // Class 1: 32-63
    // ... (rest of the ranges)
    // Class 9: 8192+
    if (size <= 31)
        return 0;
    if (size <= 63)
        return 1;
    if (size <= 127)
        return 2;
    if (size <= 255)
        return 3;
    if (size <= 511)
        return 4;
    if (size <= 1023)
        return 5;
    if (size <= 2047)
        return 6;
    if (size <= 4095)
        return 7;
    if (size <= 8191)
        return 8;
    return 9;
}

/*
 * insert_into_list - 빈 블록을 알맞은 리스트의 *앞*에 삽입 (LIFO)
 */
static void insert_into_list(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_class_index(size);
    void *head = seg_list_roots[index];

    SET_NEXT_FREE(bp, head); // bp.next = old_head
    if (head != NULL)
    {
        SET_PREV_FREE(head, bp); // old_head.prev = bp
    }
    SET_PREV_FREE(bp, NULL);    // bp.prev = NULL
    seg_list_roots[index] = bp; // root = bp
}

/*
 * remove_from_list - 리스트에서 빈 블록 제거
 */
static void remove_from_list(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_class_index(size);

    void *prev_free = GET_PREV_FREE(bp);
    void *next_free = GET_NEXT_FREE(bp);

    if (prev_free == NULL) // bp가 head인 경우
    {
        seg_list_roots[index] = next_free;
    }
    else // bp가 head가 아닌 경우
    {
        SET_NEXT_FREE(prev_free, next_free);
    }

    if (next_free != NULL) // bp가 tail이 아닌 경우
    {
        SET_PREV_FREE(next_free, prev_free);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////

/*
 * mm_init - 힙 및 Segregated List 초기화
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // Epilogue header

    // Segregated list roots 초기화
    for (int i = 0; i < NUM_CLASSES; i++)
    {
        seg_list_roots[i] = NULL;
    }

    // 초기 빈 블록 생성 및 리스트 삽입
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * extend_heap - 힙 확장 및 새 빈 블록 생성/삽입
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 정렬 유지하며 크기 계산 (최소 24바이트 보장)
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (size < (3 * DSIZE))
        size = (3 * DSIZE);

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새 빈 블록 헤더/푸터 및 새 에필로그 헤더 설정
    PUT(HDRP(bp), PACK(size, 0));         // Free block header
    PUT(FTRP(bp), PACK(size, 0));         // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header

    // 이전 블록과 병합 시도 후, 최종 블록을 리스트에 삽입
    bp = coalesce(bp);    // coalesce는 병합될 블록들을 리스트에서 제거만 함
    insert_into_list(bp); // 최종 병합된 블록을 리스트에 삽입
    return bp;            // 최종 블록 포인터 반환
}

/*
 * coalesce - 인접 빈 블록 병합 (병합 시 리스트에서 제거)
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    { // Case 1
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {                                    // Case 2
        remove_from_list(NEXT_BLKP(bp)); // 다음 블록 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {                                    // Case 3
        remove_from_list(PREV_BLKP(bp)); // 이전 블록 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {                                    // Case 4
        remove_from_list(PREV_BLKP(bp)); // 이전 블록 제거
        remove_from_list(NEXT_BLKP(bp)); // 다음 블록 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp))); // FTRP 사용 주의 -> HDRP 사용
        // size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        //         GET_SIZE(HDRP(NEXT_BLKP(bp))); // Corrected version
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // 병합된 최종 블록 포인터 반환 (아직 리스트에 삽입되지 않음)
    return bp;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_malloc - (Segregated Best-Fit)
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    // 실제 할당 크기(asize) 계산 (최소 24바이트)
    if (size <= (2 * DSIZE))
    {
        asize = 3 * DSIZE; // Min block size 24 bytes
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // Best-fit으로 블록 찾기
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // place가 리스트 제거, 분할, 나머지 삽입 담당
        return bp;
    }

    // 맞는 블록 없음 -> 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL; // extend_heap이 리스트 삽입까지 담당
    }
    place(bp, asize); // place가 리스트 제거, 분할, 나머지 삽입 담당
    return bp;
}

/*
 * find_fit - Segregated list에서 (Best-Fit)으로 블록 검색
 * (기존 로직 유지 - 주석으로 최적화 가능성 명시)
 */
static void *find_fit(size_t asize)
{
    void *bp;
    void *best_bp = NULL;
    size_t min_diff = (size_t)-1; // size_t의 최대값으로 초기화

    int list_index = get_class_index(asize);

    // 적합한 크기 클래스부터 마지막 클래스까지 탐색
    for (int i = list_index; i < NUM_CLASSES; i++)
    {
        bp = seg_list_roots[i];
        // 현재 클래스 리스트 내 모든 블록 순회
        while (bp != NULL)
        {
            size_t current_size = GET_SIZE(HDRP(bp));
            // 요청 크기(asize)보다 크거나 같은 블록을 찾으면
            if (current_size >= asize)
            {
                size_t diff = current_size - asize;
                // 기존 best_bp보다 더 작은 차이(더 좋은 fit)를 가지면 업데이트
                if (diff < min_diff)
                {
                    min_diff = diff;
                    best_bp = bp;
                    // 최적화: 만약 diff가 0이면 완벽한 fit이므로 더 이상 찾을 필요 없음
                    if (diff == 0)
                    {
                        return best_bp; // 즉시 반환 (처리율 향상)
                    }
                }
            }
            bp = GET_NEXT_FREE(bp); // 리스트의 다음 노드로 이동
        }
        /*
         * 처리율 향상을 위한 추가적인 최적화 고려 지점:
         * 1. 현재 리스트(i)에서 best_bp를 찾았다고 해서 탐색을 중단하면
         * True Best-Fit이 아니게 되어 이용률이 저하될 수 있음.
         * (더 큰 다음 리스트(i+1)에 더 딱 맞는 블록이 있을 수 있음)
         * 2. 각 리스트에서 처음 N개의 블록만 검사하는 방식으로 속도 개선 가능 (이용률 저하 감수)
         */
    }

    // 모든 리스트 탐색 후 찾은 best_bp 반환 (못 찾았으면 NULL)
    return best_bp;
}

/*
 * place - 블록 배치 및 분할 (리스트에서 제거/삽입 담당)
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    // 1. 할당할 블록을 리스트에서 제거
    remove_from_list(bp);

    // 2. 분할 여부 결정 (남은 공간 >= 최소 크기 24B)
    if ((csize - asize) >= (3 * DSIZE))
    {
        // 2a. 할당 부분 설정
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 2b. 나머지 부분 설정
        void *remainder_bp = NEXT_BLKP(bp);
        PUT(HDRP(remainder_bp), PACK(csize - asize, 0));
        PUT(FTRP(remainder_bp), PACK(csize - asize, 0));

        // 2c. 나머지 부분을 리스트에 삽입
        insert_into_list(remainder_bp);
    }
    else
    {
        // 3. 분할 안 함 -> 전체 블록 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_free - 메모리 반환 및 리스트 삽입
 */
void mm_free(void *bp)
{
    // Double free 방지
    if (bp == NULL || GET_ALLOC(HDRP(bp)) == 0)
    {
        // fprintf(stderr, "Error: Attempt to free invalid pointer %p or double free\n", bp);
        return;
    }

    size_t size = GET_SIZE(HDRP(bp));

    // 블록을 free 상태로 만듦
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 인접 블록과 병합 시도 후, 최종 블록을 리스트에 삽입
    bp = coalesce(bp);    // coalesce는 병합될 블록들을 리스트에서 제거만 함
    insert_into_list(bp); // 최종 병합된 블록을 리스트에 삽입
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_realloc - realloc 구현
 */
/* mm_realloc 함수만 표시 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t old_size;
    size_t new_asize;
    size_t copySize;
    size_t remainder_size;

    // --- 기본 예외 처리 ---
    if (size == 0)
    {
        mm_free(oldptr);
        return NULL;
    }
    if (oldptr == NULL)
    {
        return mm_malloc(size);
    }

    // --- 새 블록 크기 계산 ---
    if (size <= (2 * DSIZE))
    {
        new_asize = MIN_BLOCK_SIZE;
    }
    else
    {
        new_asize = ALIGN(size + DSIZE);
    }

    old_size = GET_SIZE(HDRP(oldptr));

    // --- Case 1: Shrinking or Same ---
    if (new_asize <= old_size)
    {
        remainder_size = old_size - new_asize;
        if (remainder_size >= MIN_BLOCK_SIZE)
        {
            PUT(HDRP(oldptr), PACK(new_asize, 1));
            PUT(FTRP(oldptr), PACK(new_asize, 1));
            void *remainder_bp = NEXT_BLKP(oldptr);
            PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
            PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
            insert_into_list(coalesce(remainder_bp));
        }
        return oldptr;
    }

    // --- Case 2: Growing ---
    else
    {
        void *prev_bp = PREV_BLKP(oldptr);
        void *next_bp = NEXT_BLKP(oldptr);
        size_t prev_alloc = GET_ALLOC(FTRP(prev_bp));
        size_t next_alloc = GET_ALLOC(HDRP(next_bp));
        size_t prev_size = GET_SIZE(FTRP(prev_bp));
        size_t next_size = GET_SIZE(HDRP(next_bp));
        size_t combined_size;

        // [!!! NEW OPTIMIZATION !!!] Subcase 2_heap_end: 현재 블록이 힙의 마지막인가?
        if (next_size == 0)
        { // 다음 블록이 에필로그 헤더인가?
            size_t extend_size = new_asize - old_size;
            // 필요한 만큼만 힙 확장 시도
            if (mem_sbrk(extend_size) != (void *)-1)
            {
                PUT(HDRP(oldptr), PACK(new_asize, 1));    // 헤더 크기 업데이트
                PUT(FTRP(oldptr), PACK(new_asize, 1));    // 푸터 크기 업데이트 (위치도 바뀜)
                PUT(HDRP(NEXT_BLKP(oldptr)), PACK(0, 1)); // 새 에필로그 헤더 설정
                return oldptr;                            // 기존 포인터 반환
            }
            // 힙 확장 실패 시, 아래 일반 로직으로 fallback
        }

        // Subcase 2a: 다음 블록만 free이고 합치면 충분
        if (!next_alloc && (combined_size = old_size + next_size) >= new_asize)
        {
            remove_from_list(next_bp);
            PUT(HDRP(oldptr), PACK(combined_size, 1));
            PUT(FTRP(oldptr), PACK(combined_size, 1));
            remainder_size = combined_size - new_asize;
            if (remainder_size >= MIN_BLOCK_SIZE)
            {
                PUT(HDRP(oldptr), PACK(new_asize, 1));
                PUT(FTRP(oldptr), PACK(new_asize, 1));
                void *remainder_bp = NEXT_BLKP(oldptr);
                PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
                PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
                insert_into_list(coalesce(remainder_bp));
            }
            return oldptr;
        }

        // Subcase 2b: 이전 블록만 free이고 합치면 충분
        else if (!prev_alloc && (combined_size = old_size + prev_size) >= new_asize)
        {
            remove_from_list(prev_bp);
            PUT(HDRP(prev_bp), PACK(combined_size, 1));
            PUT(FTRP(oldptr), PACK(combined_size, 1));
            copySize = old_size - DSIZE;
            memmove(prev_bp, oldptr, copySize);
            remainder_size = combined_size - new_asize;
            if (remainder_size >= MIN_BLOCK_SIZE)
            {
                PUT(HDRP(prev_bp), PACK(new_asize, 1));
                PUT(FTRP(prev_bp), PACK(new_asize, 1));
                void *remainder_bp = NEXT_BLKP(prev_bp);
                PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
                PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
                insert_into_list(coalesce(remainder_bp));
            }
            return prev_bp;
        }

        // Subcase 2c: 양쪽 블록 모두 free이고 합치면 충분
        else if (!prev_alloc && !next_alloc && (combined_size = old_size + prev_size + next_size) >= new_asize)
        {
            remove_from_list(prev_bp);
            remove_from_list(next_bp);
            PUT(HDRP(prev_bp), PACK(combined_size, 1));
            PUT(FTRP(next_bp), PACK(combined_size, 1));
            copySize = old_size - DSIZE;
            memmove(prev_bp, oldptr, copySize);
            remainder_size = combined_size - new_asize;
            if (remainder_size >= MIN_BLOCK_SIZE)
            {
                PUT(HDRP(prev_bp), PACK(new_asize, 1));
                PUT(FTRP(prev_bp), PACK(new_asize, 1));
                void *remainder_bp = NEXT_BLKP(prev_bp);
                PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
                PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
                insert_into_list(coalesce(remainder_bp));
            }
            return prev_bp;
        }

        // --- Subcase 2d: 최적화 실패 -> 새로 할당하고 복사 ---
        else
        {
            newptr = mm_malloc(size);
            if (newptr == NULL)
                return NULL;
            copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
            if (size < copySize)
                copySize = size;
            memcpy(newptr, oldptr, copySize);
            mm_free(oldptr);
            return newptr;
        }
    }
}