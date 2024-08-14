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
#define ALIGNMENT  // 메모리 정렬 단위

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // 주어진 alignment로 올림 처리


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t 타입의 크기로 alignment로 정렬한 값을 저장

/* Basic contstants and macro*/
#define WSIZE 4 // Word(4바이트) header, footer size
#define DSIZE 8 // Double word size(8바이트)
#define CHUNKSIZE (1<<12) // 힙을 확장 때 사용하는 기본 크기(4KB)
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) // 블록의 크기와 할당상태를 하나의 워드로 결합

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p)) // 주어진 주소 p에서 4바이트 값을 읽어옴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주어진 주소 p에 값을 기록

/* Read the size and allocated field from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // 할당 상태 비트를 제거하고 순수한 크기만
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 상태만 가져옴

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE) // 주어진 블록 포인터 bp에서 블록 헤더 주소를 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 주어진 블록 포인터 bp에서 풋터 주소 계산

/* Given Block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 다음 블록의 시작 주소를 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 이전 블록의 시작 주소를 계산

static char *heap_listp;
static void *nextfit_lastp; // nextfit 적용을 위해 추가
static void *extend_heap(size_t words);
static void *coalesce(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);
    nextfit_lastp = heap_listp; // nextfit 적용을 위해 추가

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

/* extend_heap - 새 가용 블록으로 힙 확장 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words +1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/* next fit 적용 */
static void *find_fit(size_t asize) {
    /* next fit 탐색 */
    void *bp;
    
    // nextfit_lastp를 반복문 시작으로 설정(firstfit은 heap_listp기준으로 반복문하면 끝)
    for (bp = nextfit_lastp; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    // 위 반복문에서 리턴되지 않은 경우 다시 처음부터 nextfit_lastp전까지 탐색 
    for (bp = heap_listp; bp != nextfit_lastp; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; 
}

/* place 함수 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 있는 블록 사이즈

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }

    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; // 블록 크기 조정
    size_t extendsize; // 안맞으면 확장시킬 양
    char *bp;

    /* 잘못돤 요청 무시 */
    if (size == 0)
        return NULL;
    
    /* overhead, alignment 요청 포함해서 블록 크기 조정 */
    if (size<= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 맞는 free 리스트 찾기 */
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    /* 맞는게 없다면 메모리를 더가져와서 블록에 위치 시키기 */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

    // 원래 코드 
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0)); // 헤더 0으로 표시
    PUT(FTRP(ptr), PACK(size, 0)); // 푸터 0으로 표시
    coalesce(ptr); // 비어있는 메모리 통합 
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 이전 블록의 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 다음 블록의 할당 상태
    size_t size  = GET_SIZE(HDRP(bp));  // 현재 블록의 크기

    if (prev_alloc && next_alloc) {  // 경우 1: 이전 블록과 다음 블록이 모두 할당됨
        nextfit_lastp = bp; // nextfit 적용하기 위해서 리턴전에 현재 bp를 담아줌
        return bp;  // 현재 블록만 반환 (병합할 블록이 없음)
    }

    else if (prev_alloc && !next_alloc) {  // 경우 2: 이전 블록은 할당됨, 다음 블록은 비어있음
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 현재 블록과 다음 블록 통합
        PUT(HDRP(bp), PACK(size, 0));  // 현재 블록의 헤더 업데이트
        PUT(FTRP(bp), PACK(size, 0));  // 현재 블록의 푸터 업데이트
    }

    else if (!prev_alloc && next_alloc) {  // 경우 3: 이전 블록은 비어있고, 다음 블록은 할당됨
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 현재 블록과 이전 블록 통합
        PUT(FTRP(bp), PACK(size, 0));  // 현재 블록의 푸터 업데이트
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록의 헤더 업데이트
        bp = PREV_BLKP(bp);  // 포인터를 이전 블록으로 이동
    }

    else {  // 경우 4: 이전 블록과 다음 블록 모두 비어있음
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));  // 현재 블록, 이전 블록, 다음 블록을 통합
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록의 헤더 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));  // 다음 블록의 푸터 업데이트
        bp = PREV_BLKP(bp);  // 포인터를 병합된 블록의 시작으로 이동
    }

    nextfit_lastp = bp; // nextfit 적용하기 위해서 리턴전에 현재 bp를 담아줌
    return bp;  // 병합된 블록의 포인터를 반환\

    
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t new_size = size + (2 * WSIZE);
    
    if (new_size <= old_size) {
        return ptr;
    } else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        size_t plus_next_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr)));

        if (!next_alloc && plus_next_size >= new_size) {
            PUT(HDRP(ptr), PACK(plus_next_size, 1));
            PUT(FTRP(ptr), PACK(plus_next_size, 1));
            return ptr;
        } else {
            void *new_ptr = mm_malloc(new_size);
            place(new_ptr, new_size);
            memcpy(new_ptr, ptr, new_size);
            mm_free(ptr);
            return new_ptr;
        }
    }
// 재할당의 대부분의 경우에서 memcpy를 사용하던 방법
//     if (ptr == NULL) { // 기존 위치가 없으면 바로 재할당 공간 생성 
//         return mm_malloc(size);
//     }

//     if (size <= 0) { // 요청 사이즈가 0이거나 0보다 작으면 메모리 공간 free
//         mm_free(ptr); 
//         return NULL;
//     }

//     void *oldptr = ptr; // 원래 메모리 블록 주소 
//     void *newptr = mm_malloc(size); // size만큼 새로운 메모리 블록 할당 및 주소

//     if (newptr == NULL) {
//         return NULL;
//     }
 
//     size_t copySize = GET_SIZE(HDRP(ptr)); // 재할당 전 사이즈

//     if (size < copySize) { // 요청 사이즈가 기존 사이즈보다 요청 사이즈 만큼만 데이터 잘리서 옮기기
//         copySize = size; 
//     }
    
//     memcpy(newptr, oldptr, copySize); // 새로운 공간으로 데이터 옮기기
//     mm_free(oldptr);
//     return newptr;
// 
}














