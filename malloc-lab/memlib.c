/*
 * memlib.c - a module that simulates the memory system.  Needed because it
 *            allows us to interleave calls from the student's malloc package
 *            with the system's malloc package in libc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>

#include "memlib.h"
#include "config.h"

/* private variables */
static char *mem_start_brk; /* points to first byte of heap */
static char *mem_brk;       /* points to last byte of heap */
static char *mem_max_addr;  /* largest legal heap address */

/*
 * mem_init - initialize the memory system model
 */
void mem_init(void)
{
    /* allocate the storage we will use to model the available VM */
    if ((mem_start_brk = (char *)malloc(MAX_HEAP)) == NULL)
    {
        fprintf(stderr, "mem_init_vm: malloc error\n");
        exit(1);
    }

    mem_max_addr = mem_start_brk + MAX_HEAP; /* max legal heap address */
    mem_brk = mem_start_brk;                 /* heap is empty initially */
}

/*
 * mem_deinit - free the storage used by the memory system model
 */
// mem_init()로 할당한 시뮬레이션 힙을 해제합니다.
void mem_deinit(void)
{
    free(mem_start_brk);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
 */
// mem_reset_brk() → 힙 초기화
void mem_reset_brk()
{
    mem_brk = mem_start_brk;
}

/*
 * mem_sbrk - simple model of the sbrk function. Extends the heap
 *    by incr bytes and returns the start address of the new area. In
 *    this model, the heap cannot be shrunk.
 */
void *mem_sbrk(int incr) // incr : 늘리려는 바이트 크기
{
    // 1. 할당 전 끝 주소를 old_brk 초기회 및 늘렸을 때, Max 넘어서는지 검사용
    char *old_brk = mem_brk;

    // 2. 음수 바이트 할당 오류 || 최대를 넘어선다면, => 오류
    if ((incr < 0) || ((mem_brk + incr) > mem_max_addr))
    {

        // 12	/* Out of memory */
        errno = ENOMEM;
        fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
        // 오류 반환값 :
        // 질문 : 앞으로 오류는 이딴식으로 반환하면 됨?
        return (void *)-1;
    }
    mem_brk += incr;
    // mem_brk를 반환하는 것이 아닌 시작 주소를 반환
    // 이유 : 할당 후, 그 할당된 메모리 안에 값을 시작점부터 넣어야 하기 때문
    return (void *)old_brk;
}

/*
 * mem_heap_lo - return address of the first heap byte
 */
void *mem_heap_lo()
{
    return (void *)mem_start_brk;
}

/*
 * mem_heap_hi - return address of last heap byte
 */
void *mem_heap_hi()
{
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
 */
size_t mem_heapsize()
{
    return (size_t)(mem_brk - mem_start_brk);
}

/*
 * mem_pagesize() - returns the page size of the system
 */
size_t mem_pagesize()
{
    return (size_t)getpagesize();
}
