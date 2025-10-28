/*
 * mm-segregated.c - Segregated explicit free lists (best-fit) 기반 malloc 구현
 *
 * --- 변경된 구조 ---
 *
 * [할당된 블록] (최소 16B - 교재 기준, 여기서는 24B가 될 수 있음. asize 계산 참조)
 * -----------------------------------------------------
 * | header (4B) | payload ... | footer (4B) |
 * -----------------------------------------------------
 *
 * [비어있는 블록 (최소 24B)]
 * -----------------------------------------------------------------
 * | header (4B) | prev_ptr (8B) | next_ptr (8B) | ... | footer (4B) |
 * -----------------------------------------------------------------
 * - 비어있는 블록의 payload 영역은 'prev_ptr'과 'next_ptr' 포인터(총 16B)로 사용됨.
 * - Header(4B) + Pointers(16B) + Footer(4B) = 최소 24 바이트.
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

/* 힙의 모든 블록은 8바이트 경계로 정렬되어야 함 */
#define ALIGNMENT 8
/* 주어진 size를 8바이트의 배수로 올림(align)하는 매크로 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
/* 1 워드(Word) 크기, 헤더/푸터의 크기 (4바이트) */
#define WSIZE 4
/* 2 워드(Double Word) 크기, 정렬 단위 (8바이트) */
#define DSIZE 8
/* 힙을 확장할 때 사용할 기본 크기 (4KB) */
#define CHUNKSIZE (1 << 12)

/* 두 값 중 큰 값을 반환 (realloc에서 힙 확장 크기 결정 시 사용) */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 헤더/푸터에 저장할 값 생성. 'size'와 'alloc' 비트(0 또는 1)를 OR 연산으로 합침 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서 4바이트(1 워드) 값을 읽어옴. (void *)를 역참조하기 위해 캐스팅 */
#define GET(p) (*(unsigned int *)(p))
/* 주소 p에 4바이트 값(val)을 씀 */
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p(헤더/푸터)에서 '크기' 정보만 추출. (하위 3비트를 0으로 만듦) */
#define GET_SIZE(p) (GET(p) & ~0x7)
/* 주소 p(헤더/푸터)에서 '할당 비트'(0x1)만 추출 */
#define GET_ALLOC(p) (GET(p) & 0x1)

/*
 * bp(Block Pointer)는 *페이로드*의 시작 주소를 가리킴.
 * HDRP(bp): bp에서 WSIZE(4B)만큼 *앞으로* 이동하여 해당 블록의 헤더 주소를 계산.
 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
/*
 * FTRP(bp): bp에서 헤더의 크기만큼 *뒤로* 간 후, DSIZE(8B)만큼 *앞으로* 와서 푸터 주소를 계산.
 * (bp + block_size - 8)
 * (block_size = 헤더(4B) + 페이로드 + 패딩 + 푸터(4B))
 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*
 * NEXT_BLKP(bp): 현재 블록(bp)의 헤더에서 '크기'를 읽어와,
 * bp에서 그 크기만큼 *뒤로* 이동하여 '다음' 블록의 페이로드 시작 주소를 계산.
 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
/*
 * PREV_BLKP(bp): 현재 블록(bp)에서 DSIZE(8B)만큼 *앞으로* 이동하여 '이전' 블록의 푸터 주소를 찾음.
 * 그 푸터에서 '이전' 블록의 크기를 읽어와, bp에서 그 크기만큼 *앞으로* 이동하여 '이전' 블록의 페이로드 시작 주소를 계산.
 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/* --- NEW: Segregated List를 위한 매크로 및 상수 --- */

/*
 * 64비트 환경이므로 포인터는 8바이트(DSIZE).
 * '빈 블록'의 페이로드 시작 주소(bp)에 '이전 빈 블록'의 포인터를 저장/로드.
 */
#define GET_PREV_FREE(bp) (*(void **)(bp))
#define SET_PREV_FREE(bp, ptr) (*(void **)(bp) = (ptr))
/*
 * '빈 블록'의 페이로드 시작 주소(bp) + 8바이트 위치에 '다음 빈 블록'의 포인터를 저장/로드.
 */
#define GET_NEXT_FREE(bp) (*(void **)((char *)(bp) + DSIZE))
#define SET_NEXT_FREE(bp, ptr) (*(void **)((char *)(bp) + DSIZE) = (ptr))

/*
 * 크기 클래스(버킷)의 총 개수. (0 ~ 9)
 */
#define NUM_CLASSES 10
/* --- NEW --- */
/* --- 추가 매크로 --- */
/*
 * 최소 블록 크기 정의.
 * Header(4B) + Prev Ptr(8B) + Next Ptr(8B) + Footer(4B) = 24 바이트.
 */
#define MIN_BLOCK_SIZE (3 * DSIZE)
////////////////////////////////////////////////////////////////////////////////////////////////////////
/* --- 전역 변수 --- */
/* 힙의 시작(패딩)을 가리키는 포인터. mm_init에서만 설정됨. */
static char *heap_listp = 0;
/*
 * Segregated List의 각 크기 클래스(총 10개)의 시작(root)을 가리키는 포인터 배열.
 * seg_list_roots[0]는 24-31B 크기 리스트의 첫 번째 빈 블록을 가리킴.
 * seg_list_roots[1]는 32-63B 크기 리스트의 첫 번째 빈 블록을 가리킴. ...
 */
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
 * get_class_index - 주어진 size가 속해야 할 리스트의 인덱스(0~9)를 반환
 * Segregated free list(분리된 빈 블록 리스트)를 사용시,내  빈 블록들을 크기별로 여러 리스트에 나눠 관리
 */
static int get_class_index(size_t size)
{
    /* 크기 클래스 분배 (24가 최소) */
    /* Class 0: 24-31 */
    if (size <= 31)
        return 0;
    /* Class 1: 32-63 */
    if (size <= 63)
        return 1;
    /* Class 2: 64-127 */
    if (size <= 127)
        return 2;
    /* Class 3: 128-255 */
    if (size <= 255)
        return 3;
    /* Class 4: 256-511 */
    if (size <= 511)
        return 4;
    /* Class 5: 512-1023 */
    if (size <= 1023)
        return 5;
    /* Class 6: 1024-2047 */
    if (size <= 2047)
        return 6;
    /* Class 7: 2048-4095 */
    if (size <= 4095)
        return 7;
    /* Class 8: 4096-8191 */
    if (size <= 8191)
        return 8;
    /* Class 9: 8192+ */
    return 9;
}

/*
 * insert_into_list - 빈 블록(bp)을 알맞은 크기 클래스 리스트의 *맨 앞*에 삽입 (LIFO)
 */
static void insert_into_list(void *bp)
{
    /* 1. 블록 크기에 맞는 리스트 인덱스 찾기 */
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_class_index(size);
    /* 2. 해당 리스트의 현재 첫 번째 블록(head) 가져오기 */
    void *head = seg_list_roots[index];

    /* 3. bp를 새로운 head로 만들기 (LIFO) */
    /* 3a. bp의 '다음' 포인터가 '이전 head'를 가리키게 함 */
    SET_NEXT_FREE(bp, head);
    /* 3b. 만약 '이전 head'가 존재했다면, '이전 head'의 '이전' 포인터가 bp를 가리키게 함 */
    if (head != NULL)
    {
        SET_PREV_FREE(head, bp);
    }
    /* 3c. bp는 이제 head이므로, '이전' 포인터는 NULL */
    SET_PREV_FREE(bp, NULL);
    /* 3d. 리스트의 루트(시작) 포인터를 bp로 교체 */
    seg_list_roots[index] = bp;
}

/*
 * remove_from_list - 리스트에서 빈 블록(bp) 제거 (연결 해제)
 */
static void remove_from_list(void *bp)
{
    /* 1. 블록 크기에 맞는 리스트 인덱스 찾기 */
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_class_index(size);

    /* 2. bp의 '이전' 빈 블록과 '다음' 빈 블록 포인터 가져오기 */
    void *prev_free = GET_PREV_FREE(bp);
    void *next_free = GET_NEXT_FREE(bp);

    /* 3. bp가 리스트의 head였을 경우 (prev_free == NULL) */
    if (prev_free == NULL)
    {
        /* 3a. 리스트의 루트(시작)를 bp의 '다음' 블록으로 변경 */
        seg_list_roots[index] = next_free;
    }
    /* 4. bp가 head가 아닐 경우 */
    else
    {
        /* 4a. '이전' 블록의 '다음' 포인터를 bp의 '다음' 블록으로 변경 (bp 건너뛰기) */
        SET_NEXT_FREE(prev_free, next_free);
    }

    /* 5. bp가 리스트의 tail이 아닐 경우 (next_free != NULL) */
    if (next_free != NULL)
    {
        /* 5a. '다음' 블록의 '이전' 포인터를 bp의 '이전' 블록으로 변경 (bp 건너뛰기) */
        SET_PREV_FREE(next_free, prev_free);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////

/*
 * mm_init - 힙 및 Segregated List 초기화
 */
int mm_init(void)
{
    /* [이전 답변 참고] 16바이트를 요청하여 패딩, 프롤로그(H/F), 에필로그(H) 설치 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    /* heap_listp 포인터를 프롤로그의 페이로드 위치(주소 8)로 이동시키는 원본 코드.
     * Segregated-fit에서는 전역 `heap_listp`를 `find_fit`에서 직접 쓰진 않지만,
     * `extend_heap`이 최초 호출될 때 `coalesce`가 `PREV_BLKP`를 쓰므로 필요함.
     * -> 이 코드베이스에서는 `heap_listp`를 전역 변수(주소 0)로만 쓰고
     * `PREV_BLKP` 등이 프롤로그/에필로그에 의존하게 둠.
     * (주석: 교재의 implicit list 구현에서는 heap_listp += (2*WSIZE)가 있었으나
     * 이 코드(segregated)는 heap_listp를 힙의 실제 시작(@0)으로 사용하는 것으로 보임.
     * 이는 PREV_BLKP/NEXT_BLKP가 bp 기준이 아닌, HDRP/FTRP가 bp 기준이기 때문에
     * `heap_listp` 자체를 순회 시작점으로 쓰지 않는 한 문제없음.)
     */

    /* --- NEW --- */
    /* seg_list_roots 배열의 모든 포인터를 NULL로 초기화 */
    for (int i = 0; i < NUM_CLASSES; i++)
    {
        seg_list_roots[i] = NULL;
    }
    /* --- END NEW --- */

    /* * 힙을 CHUNKSIZE(4KB)만큼 확장하여 첫 번째 빈 블록을 생성.
     * extend_heap은 내부적으로 coalesce와 insert_into_list를 호출함.
     */
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

    /* 1. 요청받은 words를 8바이트(DSIZE) 배수로 올림(align) */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    /* 2. 크기가 최소 블록 크기(24B)보다 작은지 확인, 작으면 24B로 강제 */
    if (size < MIN_BLOCK_SIZE)
        size = MIN_BLOCK_SIZE;

    /* 3. mem_sbrk로 힙 확장. bp는 새 블록의 페이로드 시작 주소. */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL; /* 실패 */

    /* 4. 새 빈 블록의 헤더/푸터 설정 (할당 비트 0) */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    /* 5. 새 힙의 끝에 새 에필로그 헤더(0/1) 설치 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /*
     * 6. 이전 블록이 free였을 경우 병합 시도.
     * coalesce는 병합될 블록들을 리스트에서 *제거*하고 병합된 블록 포인터(bp)를 반환.
     */
    bp = coalesce(bp);
    /* 7. 최종 병합된 블록을 빈 리스트에 *삽입*. */
    insert_into_list(bp);
    /* 8. 새 빈 블록(또는 병합된 블록)의 포인터 반환 */
    return bp;
}

/*
 * coalesce - 인접 빈 블록 병합 (병합 시 리스트에서 제거)
 */
static void *coalesce(void *bp)
{
    /* 이전 블록의 할당 상태 (푸터에서 확인) */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    /* 다음 블록의 할당 상태 (헤더에서 확인) */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /* 현재 블록(bp)의 크기 */
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: 이전, 다음 블록 모두 할당됨 */
    if (prev_alloc && next_alloc)
    {
        return bp; /* 아무것도 안 하고 bp 반환 */
    }
    /* Case 2: 이전(할당됨), 다음(비어있음) -> 현재(bp)와 다음 병합 */
    else if (prev_alloc && !next_alloc)
    {
        remove_from_list(NEXT_BLKP(bp));       /* 다음 블록을 리스트에서 제거 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); /* 현재 크기에 다음 블록 크기 더함 */
        PUT(HDRP(bp), PACK(size, 0));          /* 현재 블록(bp)의 헤더 업데이트 */
        PUT(FTRP(bp), PACK(size, 0));          /* 현재 블록(bp)의 푸터 업데이트 */
        /* bp는 변경 없음 */
    }
    /* Case 3: 이전(비어있음), 다음(할당됨) -> 이전과 현재(bp) 병합 */
    else if (!prev_alloc && next_alloc)
    {
        remove_from_list(PREV_BLKP(bp));         /* 이전 블록을 리스트에서 제거 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   /* 현재 크기에 이전 블록 크기 더함 */
        PUT(FTRP(bp), PACK(size, 0));            /* 현재 블록(bp)의 푸터 업데이트 (새 끝) */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); /* 이전 블록의 헤더 업데이트 (새 시작) */
        bp = PREV_BLKP(bp);                      /* bp를 이전 블록(병합된 블록의 시작)으로 이동 */
    }
    /* Case 4: 이전(비어있음), 다음(비어있음) -> 이전, 현재(bp), 다음 모두 병합 */
    else
    {
        remove_from_list(PREV_BLKP(bp)); /* 이전 블록 제거 */
        remove_from_list(NEXT_BLKP(bp)); /* 다음 블록 제거 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(HDRP(NEXT_BLKP(bp)));   /* (주석: GET_SIZE(FTRP(...)) 원본 코드 수정) */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); /* 이전 블록 헤더 업데이트 (새 시작) */
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); /* 다음 블록 푸터 업데이트 (새 끝) */
        bp = PREV_BLKP(bp);                      /* bp를 이전 블록(병합된 블록의 시작)으로 이동 */
    }
    /* 병합된 블록의 시작 포인터(bp) 반환 */
    return bp;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_malloc - (Segregated Best-Fit)
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* 실제 할당할 조정된 블록 크기 */
    size_t extendsize; /* 힙 확장 크기 */
    char *bp;          /* 블록 포인터 */

    /* 1. 요청 크기가 0이면 무시 (NULL 반환) */
    if (size == 0)
        return NULL;

    /* 2. 실제 할당 크기(asize) 계산 (최소 24바이트 보장) */
    if (size <= (2 * DSIZE)) /* 요청이 16B(prev+next 포인터 공간)보다 작거나 같으면 */
    {
        asize = MIN_BLOCK_SIZE; /* 최소 크기 24B 할당 (H+F+prev+next) */
    }
    else
    {
        /* 요청 size + 헤더/푸터(DSIZE) + 정렬을 위해 올림(ALIGN) */
        asize = ALIGN(size + DSIZE);
        /* (주석: (size + (DSIZE) + (DSIZE - 1)) / DSIZE) * DSIZE 와 동일) */
    }

    /* 3. Best-fit으로 빈 블록 리스트에서 적절한 블록(bp) 찾기 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); /* 찾은 블록에 배치(및 분할) */
        return bp;        /* 새 블록의 페이로드 포인터 반환 */
    }

    /* 4. (find_fit 실패) 맞는 블록이 없으면 힙 확장 */
    /* 확장 크기는 (요청한 asize)와 (기본 CHUNKSIZE) 중 더 큰 값 */
    extendsize = MAX(asize, CHUNKSIZE);
    /* extend_heap 호출 (내부적으로 coalesce + insert_into_list 수행) */
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL; /* 힙 확장에 실패하면 NULL (메모리 고갈) */
    }
    /* 5. 새로 확장된 빈 블록(bp)에 배치 */
    place(bp, asize); /* (place는 이 블록을 리스트에서 제거하고 할당함) */
    return bp;        /* 새 블록의 페이로드 포인터 반환 */
}

/*
 * find_fit - Segregated list에서 (Best-Fit)으로 블록 검색
 */
static void *find_fit(size_t asize)
{
    void *bp;             /* 리스트 순회용 포인터 */
    void *best_bp = NULL; /* 현재까지 찾은 최적의 블록 포인터 */
    /* 현재까지 찾은 최적의 (csize - asize) 차이. (최대값으로 초기화) */
    size_t min_diff = (size_t)-1;

    /* 1. 요청한 크기(asize)가 속하는 크기 클래스 인덱스 찾기 */
    int list_index = get_class_index(asize);

    /* 2. 해당 인덱스부터 마지막 클래스까지 순서대로 리스트 탐색 */
    for (int i = list_index; i < NUM_CLASSES; i++)
    {
        bp = seg_list_roots[i]; /* 현재 클래스 리스트의 head */
        /* 3. 현재 리스트의 끝(NULL)까지 모든 빈 블록 순회 */
        while (bp != NULL)
        {
            size_t current_size = GET_SIZE(HDRP(bp));
            /* 4. 현재 블록이 요청 크기(asize)보다 크거나 같으면 (후보) */
            if (current_size >= asize)
            {
                size_t diff = current_size - asize; /* 낭비되는 공간(차이) 계산 */
                /* 5. 이 차이(diff)가 이전에 찾은 최소 차이(min_diff)보다 작으면 (더 Best) */
                if (diff < min_diff)
                {
                    min_diff = diff; /* 최소 차이 갱신 */
                    best_bp = bp;    /* 최적 블록 갱신 */

                    /* 6. [최적화] 만약 차이가 0이면 (완벽한 fit), 더 찾을 필요 없음 */
                    if (diff == 0)
                        return best_bp; /* 즉시 반환 (처리율 향상) */
                }
            }
            bp = GET_NEXT_FREE(bp); /* 리스트의 다음 빈 블록으로 이동 */
        }
    }

    /* 7. 모든 리스트 탐색 후 찾은 best_bp 반환 (못 찾았으면 NULL) */
    return best_bp;
}

/*
 * place - 찾은 빈 블록(bp)에 요청한 크기(asize)를 배치 (및 분할)
 */
static void place(void *bp, size_t asize)
{
    /* 1. 배치할 빈 블록의 전체 크기(csize) 가져오기 */
    size_t csize = GET_SIZE(HDRP(bp));

    /* 2. 이 블록은 이제 할당될 것이므로, 빈 리스트에서 *제거* */
    remove_from_list(bp);

    /* 3. (csize - asize) (남는 공간)가 최소 블록 크기(24B)보다 크거나 같은가? */
    if ((csize - asize) >= MIN_BLOCK_SIZE)
    {
        /* 4. (Yes) 블록 분할(Split) 수행 */
        /* 4a. 앞부분(asize)은 '할당됨(1)'으로 헤더/푸터 설정 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* 4b. 뒷부분(남은 블록)의 포인터 계산 */
        void *remainder_bp = NEXT_BLKP(bp);
        /* 4c. 남은 블록의 헤더/푸터를 '비어있음(0)'으로 설정 */
        PUT(HDRP(remainder_bp), PACK(csize - asize, 0));
        PUT(FTRP(remainder_bp), PACK(csize - asize, 0));

        /* 4d. 새로 생성된 이 '남은 빈 블록'을 빈 리스트에 *삽입* */
        insert_into_list(remainder_bp);
    }
    else
    {
        /* 5. (No) 분할하지 않음. csize 전체를 '할당됨(1)'으로 설정 */
        /* (asize보다 큰 csize 전체를 사용하므로, 내부 단편화 발생) */
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
    /* 1. bp가 NULL이거나, 이미 free된 블록(할당 비트 0)이면 오류이므로 즉시 반환 */
    if (bp == NULL || GET_ALLOC(HDRP(bp)) == 0)
        return;

    /* 2. 현재 블록 크기 가져오기 */
    size_t size = GET_SIZE(HDRP(bp));

    /* 3. 헤더와 푸터의 할당 비트를 0('비어있음')으로 설정 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /*
     * 4. 인접 블록 병합 시도. coalesce는 병합된 블록의 시작 포인터 반환.
     * (coalesce 내부에서 병합되는 빈 블록들은 리스트에서 *제거*됨)
     */
    bp = coalesce(bp);
    /*
     * 5. 최종적으로 병합된 (혹은 병합되지 않은) 빈 블록(bp)을
     * 알맞은 크기 클래스 리스트에 *삽입*.
     */
    insert_into_list(bp);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * mm_realloc - realloc 구현 (병합 최적화 포함)
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;    /* 이전 블록 포인터 */
    void *newptr;          /* 새 블록 포인터 */
    size_t old_size;       /* 이전 블록의 *전체* 크기 */
    size_t new_asize;      /* 새로 요청된 size에 맞는 *조정된* 블록 크기 */
    size_t copySize;       /* 복사할 데이터(페이로드) 크기 */
    size_t remainder_size; /* 분할 후 남는 블록 크기 */

    /* --- 기본 예외 처리 --- */
    /* 1. size == 0 -> free(ptr)와 동일 */
    if (size == 0)
    {
        mm_free(oldptr);
        return NULL;
    }
    /* 2. ptr == NULL -> malloc(size)와 동일 */
    if (oldptr == NULL)
    {
        return mm_malloc(size);
    }

    /* --- 새 블록 크기 계산 --- */
    if (size <= (2 * DSIZE)) /* 16B 이하 요청 */
    {
        new_asize = MIN_BLOCK_SIZE; /* 최소 24B */
    }
    else
    {
        new_asize = ALIGN(size + DSIZE); /* size + 헤더/푸터(8B) + 정렬 */
    }

    /* 이전 블록의 전체 크기 가져오기 */
    old_size = GET_SIZE(HDRP(oldptr));

    /* --- Case 1: 새 크기(new_asize)가 이전 크기(old_size)보다 작거나 같은 경우 (축소) --- */
    if (new_asize <= old_size)
    {
        remainder_size = old_size - new_asize; /* 남는 공간 계산 */
        /* 남는 공간이 최소 블록 크기(24B)보다 크면 분할 */
        if (remainder_size >= MIN_BLOCK_SIZE)
        {
            /* 1a. 앞부분(oldptr)은 new_asize 크기로 '할당됨' 설정 */
            PUT(HDRP(oldptr), PACK(new_asize, 1));
            PUT(FTRP(oldptr), PACK(new_asize, 1));
            /* 1b. 뒷부분(남는 블록) 포인터 계산 */
            void *remainder_bp = NEXT_BLKP(oldptr);
            /* 1c. 남는 블록을 '비어있음'으로 설정 */
            PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
            PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
            /* 1d. 이 새 빈 블록을 `free`와 동일하게 처리 (병합 시도 및 리스트 삽입) */
            insert_into_list(coalesce(remainder_bp));
        }
        /* 분할 못하면(남는 공간 < 24B) 그냥 oldptr 반환 (내부 단편화) */
        return oldptr;
    }

    /* --- Case 2: 새 크기가 이전 크기보다 큰 경우 (확장) --- */
    else
    {
        /* --- 인접 블록 탐색 (최적화용) --- */
        void *prev_bp = PREV_BLKP(oldptr);
        void *next_bp = NEXT_BLKP(oldptr);
        size_t prev_alloc = GET_ALLOC(FTRP(prev_bp));
        size_t next_alloc = GET_ALLOC(HDRP(next_bp));
        size_t prev_size = GET_SIZE(FTRP(prev_bp));
        size_t next_size = GET_SIZE(HDRP(next_bp));
        size_t combined_size;

        /* [!!! REALLOC 최적화 1 !!!] (Subcase 2_heap_end)
         * 현재 블록이 힙의 마지막(다음이 에필로그)인가?
         */
        if (next_size == 0)
        {
            size_t extend_size = new_asize - old_size; /* 필요한 추가 공간 */
            /* 필요한 만큼만 mem_sbrk로 힙 확장 */
            if (mem_sbrk(extend_size) != (void *)-1)
            {
                PUT(HDRP(oldptr), PACK(new_asize, 1));    /* 헤더 크기 업데이트 */
                PUT(FTRP(oldptr), PACK(new_asize, 1));    /* 새 푸터 위치에 값 쓰기 */
                PUT(HDRP(NEXT_BLKP(oldptr)), PACK(0, 1)); /* 새 에필로그 설치 */
                return oldptr;                            /* 데이터 복사 필요 없음! */
            }
            /* 힙 확장 실패 시, 아래의 일반 로직(Subcase 2d)으로 넘어감 */
        }

        /* [!!! REALLOC 최적화 2 !!!] (Subcase 2a)
         * 다음 블록만 '비어있고', 합친 크기가 충분한가?
         */
        if (!next_alloc && (combined_size = old_size + next_size) >= new_asize)
        {
            remove_from_list(next_bp);                 /* 다음 빈 블록을 리스트에서 제거 */
            PUT(HDRP(oldptr), PACK(combined_size, 1)); /* 합친 크기로 헤더/푸터 업데이트 */
            PUT(FTRP(oldptr), PACK(combined_size, 1));

            /* 다시 분할 가능 여부 확인 */
            remainder_size = combined_size - new_asize;
            if (remainder_size >= MIN_BLOCK_SIZE)
            {
                PUT(HDRP(oldptr), PACK(new_asize, 1)); /* 앞부분(new_asize) 할당 */
                PUT(FTRP(oldptr), PACK(new_asize, 1));
                void *remainder_bp = NEXT_BLKP(oldptr); /* 뒷부분(남는 블록) free */
                PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
                PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
                insert_into_list(coalesce(remainder_bp)); /* 리스트 삽입 */
            }
            return oldptr; /* 데이터 복사 필요 없음! */
        }

        /* [!!! REALLOC 최적화 3 !!!] (Subcase 2b)
         * 이전 블록만 '비어있고', 합친 크기가 충분한가?
         */
        else if (!prev_alloc && (combined_size = old_size + prev_size) >= new_asize)
        {
            remove_from_list(prev_bp); /* 이전 빈 블록 리스트에서 제거 */
            /* (데이터 복사 먼저!) 겹칠 수 있으므로 memmove 사용 */
            copySize = old_size - DSIZE;        /* 실제 페이로드 크기 */
            memmove(prev_bp, oldptr, copySize); /* 데이터를 이전 블록 위치로 이동 */

            /* 헤더/푸터 업데이트 */
            PUT(HDRP(prev_bp), PACK(combined_size, 1));
            PUT(FTRP(prev_bp), PACK(combined_size, 1)); // FTRP(prev_bp) 사용

            /* 분할 가능 여부 확인 */
            remainder_size = combined_size - new_asize;
            if (remainder_size >= MIN_BLOCK_SIZE)
            {
                PUT(HDRP(prev_bp), PACK(new_asize, 1)); /* 앞부분 할당 */
                PUT(FTRP(prev_bp), PACK(new_asize, 1));
                void *remainder_bp = NEXT_BLKP(prev_bp); /* 뒷부분 free */
                PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
                PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
                insert_into_list(coalesce(remainder_bp)); /* 리스트 삽입 */
            }
            return prev_bp; /* (중요) 포인터가 변경되었으므로 prev_bp 반환 */
        }

        /* [!!! REALLOC 최적화 4 !!!] (Subcase 2c)
         * 양쪽 블록 모두 '비어있고', 합친 크기가 충분한가?
         */
        else if (!prev_alloc && !next_alloc && (combined_size = old_size + prev_size + next_size) >= new_asize)
        {
            remove_from_list(prev_bp); /* 이전 블록 제거 */
            remove_from_list(next_bp); /* 다음 블록 제거 */

            /* (데이터 복사 먼저!) */
            copySize = old_size - DSIZE;
            memmove(prev_bp, oldptr, copySize);

            /* 헤더/푸터 업데이트 */
            PUT(HDRP(prev_bp), PACK(combined_size, 1));
            PUT(FTRP(next_bp), PACK(combined_size, 1)); // 푸터는 next_bp의 푸터 위치

            /* 분할 가능 여부 확인 */
            remainder_size = combined_size - new_asize;
            if (remainder_size >= MIN_BLOCK_SIZE)
            {
                PUT(HDRP(prev_bp), PACK(new_asize, 1));
                PUT(FTRP(prev_bp), PACK(new_asize, 1)); // 푸터는 new_asize 위치
                void *remainder_bp = NEXT_BLKP(prev_bp);
                PUT(HDRP(remainder_bp), PACK(remainder_size, 0));
                PUT(FTRP(remainder_bp), PACK(remainder_size, 0));
                insert_into_list(coalesce(remainder_bp));
            }
            return prev_bp; /* (중요) 포인터가 변경되었으므로 prev_bp 반환 */
        }

        /* [!!! 최후의 수단 !!!] (Subcase 2d)
         * 모든 최적화 실패. 새로 할당하고, 복사하고, 이전 블록 해제.
         */
        else
        {
            newptr = mm_malloc(size); /* (주의: asize가 아닌 원본 size로 요청) */
            if (newptr == NULL)
                return NULL;

            /* 복사할 크기 계산 (이전 페이로드와 새 요청 size 중 작은 값) */
            copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
            if (size < copySize)
                copySize = size;

            memcpy(newptr, oldptr, copySize); /* 데이터 복사 */
            mm_free(oldptr);                  /* 이전 블록 해제 */
            return newptr;                    /* 새 포인터 반환 */
        }
    }
}