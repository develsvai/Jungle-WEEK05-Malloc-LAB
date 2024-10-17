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

/*
 * mm_init - initialize the malloc package.
 */
/* 기본 상수와 매크로 */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4             /* 워드 크기 */
#define DSIZE 8             /* 더블 워드 크기 */
#define CHUNKSIZE (1 << 12) /* 초기 확장 힙 크기 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 헤더와 푸터 조작 */
#define HEADER(size, alloc) ((size) | (alloc))           /* 헤더/푸터에 크기 및 할당 비트 저장 */
/* 메모리 효율성을 위해 메크로 사용
typedef struct {
    size_t size;   // 블록 크기
    int allocated; // 할당 여부
} Header;
 */

#define GET(p) (*(unsigned int *)(p))                  /* 포인터 p에 저장된 값 반환 */
#define PUT(p, val) (*(unsigned int *)(p) = (val))     /* 포인터 p에 값 저장 */
#define GET_SIZE(p) (GET(p) & ~0x7)                    /* 크기만 추출 */
#define GET_ALLOC(p) (GET(p) & 0x1)                    /* 할당 여부 추출 */

/* 블록의 주소 계산 */
#define HDR_ADDR(bp) ((char *)(bp) - WSIZE)                /* 헤더의 주소 */
#define FTR_ADDR(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* 푸터의 주소 */
#define NEXT_BLK(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) /* 다음 블록 */
#define PREV_BLP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) /* 이전 블록 */

/* 프리 리스트의 첫 번째 블록을 가리키는 포인터 */
static char *heap_listp = NULL;

/* 함수 선언 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - 힙을 초기화하고 첫 번째 빈 블록을 생성.
 */
int mm_init(void)
{


/*
    function mm_init():
        1. 요청: 힙을 4 * WSIZE(16 바이트) 크기로 확장한다.
           - 만약 메모리 확장 실패 시, 초기화 실패를 반환(-1).

        2. 정렬 패딩을 추가한다:
           - 첫 번째 워드에 0을 넣는다 (정렬을 위한 패딩).

        3. 프롤로그 블록을 생성한다:
           - 프롤로그 블록의 헤더에 DSIZE(8바이트) 크기와 '할당됨' 상태를 기록한다.
           - 프롤로그 블록의 푸터에 DSIZE(8바이트) 크기와 '할당됨' 상태를 기록한다.

        4. 에필로그 블록을 생성한다:
           - 에필로그 블록의 헤더에 크기 0과 '할당됨' 상태를 기록한다 (힙의 끝을 표시).

        5. 포인터를 프롤로그 블록 뒤로 이동한다:
           - heap_listp 포인터를 프롤로그 푸터 뒤로 설정한다.

        6. 힙을 CHUNKSIZE 크기로 확장한다:
           - 요청: 힙을 CHUNKSIZE(일정 크기, 일반적으로 시스템 의존적)만큼 확장한다.
           - 만약 확장 실패 시, 초기화 실패를 반환(-1).

        7. 초기화 성공을 반환(0).

*/

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* 정렬 패딩 */
    PUT(heap_listp + (1 * WSIZE), HEADER(DSIZE, 1)); /* 프롤로그 헤더 */
    PUT(heap_listp + (2 * WSIZE), HEADER(DSIZE, 1)); /* 프롤로그 푸터 */
    PUT(heap_listp + (3 * WSIZE), HEADER(0, 1));     /* 에필로그 헤더 */
    heap_listp += (2 * WSIZE);

    /* 힙을 CHUNKSIZE 바이트로 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * extend_heap - 힙을 확장하는 함수.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 짝수 크기로 할당하기 위해 ALIGN */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 빈 블록 헤더/푸터 및 에필로그 헤더 생성 */
    PUT(HDRP(bp), HEADER(size, 0));         /* 프리 블록 헤더 */
    PUT(FTRP(bp), HEADER(size, 0));         /* 프리 블록 푸터 */
    PUT(HDRP(NEXT_BLKP(bp)), HEADER(0, 1)); /* 새로운 에필로그 헤더 */

    /* 병합을 통해 블록 연결 */
    return coalesce(bp);
}

/*
 * coalesce - 인접한 가용 블록을 병합하는 함수.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* 이전, 다음 블록이 모두 할당 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* 다음 블록이 가용 상태 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {      /* 이전 블록이 가용 상태 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                     /* 이전, 다음 블록이 모두 가용 상태 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_malloc - 요청된 크기의 블록을 할당.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* 실제 할당 크기 */
    size_t extendsize; /* 힙 확장 크기 */
    char *bp;

    /* 잘못된 요청 처리 */
    if (size == 0)
        return NULL;

    /* 최소 블록 크기 할당 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 가용 블록 탐색 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 힙을 확장하여 메모리 할당 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * find_fit - 가용 블록을 탐색.
 */
static void *find_fit(size_t asize)
{
    void *bp;

`
    /* 첫 번째 가용 블록 탐색
    최조 적합
    */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

/*
 * place - 블록을 배치하고, 남은 부분은 분할.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - 메모리를 해제하고 병합.
 */
void mm_free(void *bp)
{
    if (bp == NULL) return;

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - 기존 블록을 재할당.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t copySize;

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }

    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copySize) {
        copySize = size;
    }
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}














