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
    "Team8",
    /* First member's full name */
    "Kim Dasol",
    /* First member's email address */
    "dsk2588@gmail.com",
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

// 기본상수와 매크로
#define WSIZE 4 // word-header-footer size
#define DSIZE 8 // double word size
#define CHUNKSIZE (1<<12) // 새로 할당 받는 힙의 크기 : (힙을 1 <<12 만큼 연장)

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 삼항연산자 

// 헤더와 풋터 값 리턴
#define PACK(size, alloc) ((size) | (alloc)) // 비트연산자(or)로, 1이 하나라도 있으면 1을 반환

// 주소 p에서 word를 읽어오거나 쓰는 함수
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 주소 p에서 블록의 size, allocated field를 읽어옴
// 8의 배수와 7을 뒤집은 1111 1000 AND 연산
#define GET_SIZE(p) (GET(p) & ~0x7) // 0x7 16진수 : 0111 -> ~0x7 : 1000 
// 8의 배수와 0000 0001과 AND 연산
#define GET_ALLOC(p) (GET(p) & 0x1) // 0x1 16진수 : 0001

// 블록 포인터 bp를 받아 헤더와 풋터의 주소를 리턴
// header 포인터 : bp의 주소를 받아서 한 워드 사이즈 앞으로 가면 헤더
#define HDRP(bp) ((char *)(bp) - WSIZE)
// footer 포인터 : bp의 주소를 받아 헤더의 포인터 사이즈 더하고, 더블 워드 사이즈(피딩_header) 앞으로 가면 풋터
// 전체 사이즈 알려면 HDRP(bp)로 전체 사이즈를 알아내야 함
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


// 블록 포인터 bp를 받아 이전 블록과 다음 블록의 주소 리턴
// 현재 블록 포인터에 (현재 bp - 워드 사이즈) => 헤더의 사이즈 더하면 다음 블록 포인터
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 현재 블록 포인터에 (bp - 더블워드) => 이전 블록 풋터를 빼면 이전 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void *heap_listp;
// 함수선언
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *first_fit(size_t asize);
static void *last_bp;
static void *next_fit(size_t asize);




/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
// 메모리 시스템에섯 4word 가져와 가용 리스트 만들고, extend_heap() 함수를 통해 CHUNCSIZE 바이트로 확장하고 초기 가용 블록을 생성해주는 역할을 한다.
{
    // padding, prologue, epilogue block 설정(최소 4워드), 설정한 heap_listp가 4워드 미만이면 -1 반환
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
        return -1;
    };
    
    // padding 영역 추가
    PUT(heap_listp, 0);
    // prologue header 1워드 할당 -> size 8
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); 
    // prologue footer 1워드 할당 -> size 8
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    // epilogue header 1워드 할당 -> size 0
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    
    // 더블워드 정렬을 사용하기 때문에 더블워드 사이즈 만큼 증가
    heap_listp += (2*WSIZE);

    // chunksize 사이즈 만큼 힙을 확장해 초기 가용 블록 생성
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    last_bp = heap_listp;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    // 8의 배수로 맞추기
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 인자를 받아와 홀수라면 +1한 후 *WSIZE, 짝수면 *WSIZE
    // mem_sbrk 함수는 mem_brk + size이고, 주소값은 int로 못받아서 long으로 형변환
    // 새로운 메모리의 첫부분을 bp
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // (NEXT_BLKP(bp)로 다음블록 bp를 찾고, WSIZE 뺴주기 =>에필로그 블록의 헤더

    return coalesce(bp);
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    // 사이즈가 0이면 할당 안함
    if (size == 0){
        return NULL;
    }
    // 사이즈가 더블워드 사이즈보다 작을때, 
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

    /*
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    // 헤더, 풋터를 0으로 할당
    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
}

static void *find_fit(size_t asize){

    // return first_fit(asize);
    return next_fit(asize);
}


static void *first_fit(size_t asize){
    void *bp;
    // hep_listp부터, 헤더 사이즈가 0이될때 까지 가용 가능할 블럭 찾기
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        // 헤더가 가용상태이고, 요청 사이즈가 헤더의 사이즈보다 작은 경우 할당
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}


static void *next_fit(size_t asize) {
    void *bp;
    for(bp = last_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            last_bp = bp;
            return bp;
        }
    }

    // 이전 탐색지점 이후부터 끝까지 탐색했으나 가용블록이 없는 경우, 처음부터 다시 탐색
    for(bp = heap_listp; bp < last_bp; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}





static void place(void *bp, size_t asize){
    // 들어갈 위치를 포인터로 받음
    size_t csize = GET_SIZE(HDRP(bp));

    // 현재 블록 사이즈 - 요청 사이즈 값이 헤더, 풋터를 포함하여 더블워드 사이즈 * 2배보다 크면 
    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // bp를 다음 블록의 bp로 갱신
        bp = NEXT_BLKP(bp);
        // 할당한 블록 이외의 블록의 할당을 0으로 변경
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    // 현재 블록 사이즈 == 요청 사이즈, 할당 여부 1로 변경
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


static void *coalesce(void *bp)
{
    // 이전블록의 풋터, 다음블록의 헤더로 가용 여부 확인 
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 블록의 전체 사이즈
    size_t size = GET_SIZE(HDRP(bp));

    // case1 : 이전, 다음 블록 모두 할당, 현재만 반환
    if (prev_alloc && next_alloc){
        last_bp = bp;
        return bp;
    }
    //case2 : 이전 블록 할당, 다음블록 미할당, 현재+다음블록 연결
    // 사이즈(현재 블록 사이즈) += 다음블록의 헤더 사이즈
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //case3 : 이전 블록 가용, 다음블록 할당, 이전+현재블록 연결
    else if (!prev_alloc && next_alloc) {
        // size(현재 블록 사이즈) += 이전블록의 헤더 사이즈
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        // 이전 블록의 해더 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // bp 값에 이전블록의 bp 값 대입
        bp = PREV_BLKP(bp);
    }
    
    //case4 : 이전블록, 다음블록 모두 미할당
    else {
        // 이전블록의 헤더 + 다음블록의 풋터
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    last_bp = bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *old_bp = bp;
    void *new_bp;
    size_t copySize;
    
    new_bp = mm_malloc(size);
    if (new_bp == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(old_bp)); //*(size_t *)((char *)old_bp - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(new_bp, old_bp, copySize);
    mm_free(old_bp);
    return new_bp;
}














