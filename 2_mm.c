
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>
#include <limits.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */



/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);     // word, header, footer size (bytes)
static const size_t dsize = 2 * wsize;          // double word size (bytes)
static const size_t min_block_size = 2 * dsize; // Minimum block size
static const size_t chunksize = (1 << 11);      // requires (chunksize % 16 == 0)

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    union
    {
        struct
        {
            struct block *prev;
            struct block *next;
        };
        char payload[0];
    };

    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

/* Global variables */
/* Pointer to first block */
static block_t *heap_listp = NULL;
/* Pointer to the root of the linked list */
block_t *root = NULL;

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool alloc_of_prev);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc, bool alloc_of_prev);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void prev_make(block_t *block, bool al_prev);
bool get_alloc_of_prev(block_t *block);

static void add(block_t *block_address);
static void list_remove(block_t *block_address);

bool mm_checkheap(int lineno);

/*
 * mm_init: initializes the heap; it is run once when heap_start == NULL.
 *          prior to any extend_heap operation, this is the heap:
 *              start            start+8           start+16
 *          INIT: | PROLOGUE_FOOTER | EPILOGUE_HEADER |
 * heap_listp ends up pointing to the epilogue header.
 */
bool mm_init(void)
{
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header
    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * malloc: allocates a block with size at least (size + dsize), rounded up to
 *         the nearest 16 bytes, with a minimum of 2*dsize. Seeks a
 *         sufficiently-large unallocated block on the heap to be allocated.
 *         If no such block is found, extends heap by the maximum between
 *         chunksize and (size + dsize) rounded up to the nearest 16 bytes,
 *         and then attempts to allocate all, or a part of, that memory.
 *         Returns NULL on failure, otherwise returns a pointer to such block.
 *         The allocated block will not be used for further allocations until
 *         freed.
 */
void *malloc(size_t size)
{
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_listp == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_printf("Malloc(%zd) --> %p\n", size, bp);
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = max(round_up(size + wsize, dsize), 32);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            dbg_printf("Malloc(%zd) --> %p\n", size, bp);
            return bp;
        }
    }

    place(block, asize);
    bp = header_to_payload(block);
    dbg_printf("Malloc(%zd) --> %p\n", size, bp);
    dbg_assert(mm_checkheap(__LINE__));
    return bp;
}

/*
 * free: Frees the block such that it is no longer allocated while still
 *       maintaining its size. Block will be available for use on malloc.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    write_header(block, size, false, get_alloc_of_prev(block));
    write_footer(block, size, false);

    coalesce(block);

    dbg_printf("Completed free(%p)\n", bp);
}

/*
 * realloc: returns a pointer to an allocated region of at least size bytes:
 *          if ptrv is NULL, then call malloc(size);
 *          if size == 0, then call free(ptr) and returns NULL;
 *          else allocates new region of memory, copies old data to new memory,
 *          and then free old block. Returns old block if realloc fails or
 *          returns new pointer on success.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc: Allocates a block with size at least (elements * size + dsize)
 *         through malloc, then initializes all bits in allocated memory to 0.
 *         Returns NULL on failure.
 */
void *calloc(size_t nmemb, size_t size)
{
    void *bp;
    size_t asize = nmemb * size;

    if (asize / nmemb != size)
        // Multiplication overflowed
        return NULL;

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size)
{
    void *bp;
    bool old_alloc = get_alloc_of_prev((block_t *)((char *)mem_heap_hi() - 7));

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_header(block, size, false, old_alloc);
    write_footer(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Coalesce: Coalesces current block with previous and next blocks if
 *           either or both are unallocated; otherwise the block is not
 *           modified. Then, insert coalesced block into the segregated list.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t *block)
{
    block_t *block_next = find_next(block);

    bool prev_alloc = get_alloc_of_prev(block);
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    // case 1: both previous and next blocks are allocated
    if (prev_alloc && next_alloc)
    {
        write_header(block, size, false, get_alloc_of_prev(block));
        write_footer(block, size, false);
        prev_make(block_next, false);
        add(block); // add current block to free list
        return block;
    }

    // case 2: previous block is allocated, next block is free
    else if (prev_alloc && !next_alloc)
    {
        size += get_size(block_next); // increase size to include next block
        write_header(block, size, false, true);
        write_footer(block, size, false);
        list_remove(block_next); // remove next block from free list
        add(block);              // add the merged block to free list
    }

    // case 3: previous block is free, next block is allocated
    else if (!prev_alloc && next_alloc)
    {
        block_t *block_prev = find_prev(block);
        size += get_size(block_prev); // increase size to include previous block
        write_header(block_prev, size, false, true);
        write_footer(block_prev, size, false);
        block = block_prev;      // update current block to previous block
        list_remove(block_prev); // remove previous block from free list
        prev_make(block_next, false);
        add(block); // add the merged block to free list
    }

    // case 4: both previous and next blocks are free
    else
    {
        block_t *block_prev = find_prev(block);
        size += get_size(block_next) + get_size(block_prev); // combine sizes of prev, current, and next blocks
        write_header(block_prev, size, false, true);
        write_footer(block_prev, size, false);
        block = block_prev;      // update current block to previous block
        list_remove(block_prev); // remove previous block from free list
        list_remove(block_next); // remove next block from free list
        add(block);              // add the merged large block to free list
    }
    return block; // return the coalesced block
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    // Check if the remaining space after allocation is large enough to form a new block
    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;

        // Mark the current block as allocated
        write_header(block, asize, true, true);

        // Find and prepare the next block as a new free block
        block_next = find_next(block);
        write_header(block_next, csize - asize, false, true);
        write_footer(block_next, csize - asize, false);

        // Add the new free block to the free list
        add(block_next);
    }
    else
    {
        // If the remaining space is not large enough, allocate the entire block
        write_header(block, csize, true, true);

        // Update the allocation status of the next block
        prev_make(find_next(block), true);
    }

    // Remove the current block from the free list, as it's now allocated
    list_remove(block);
}

// Function to add a block to the free list
static void add(block_t *block)
{
    // Check if the block to be added is not the root itself
    // This prevents creating a cycle in the list if the root is passed in
    if (block != root)
    {
        // Set the new block's next pointer to the current root
        // This inserts the block before the first element of the list
        block->next = root;

        // If the list is not empty (root is not NULL),
        // set the current root's previous pointer to the new block
        if (root != NULL)
            root->prev = block;

        // Move the root pointer to point to the new block,
        // effectively making it the first block in the list
        root = block;

        // Since the new block is now at the beginning,
        // set its previous pointer to NULL
        root->prev = NULL;
    }
}

// Function to remove a block from the free list
static void list_remove(block_t *block)
{
    // if block and root are the same
    if (block == root)
    {
        root = root->next;
        if (root != NULL && root->prev != NULL)
            root->prev = NULL;
    }
    else
    {
        // Update the prev pointer of the next free block
        block->prev->next = block->next;
        // Update the next pointer of the previous free block
        if (block->next != NULL)
            block->next->prev = block->prev;
        return;
    }
}

/*
 * find_fit:
 * Searches for the best_fit_block-fitting block within the free list.
 * Implements a best_fit_block-fit policy to find a block of
 * at least 'asize' bytes.
 * Returns a pointer to the block if found, otherwise NULL.
 */
static block_t *find_fit(size_t asize)
{
    block_t *best_fit_block = NULL;
    block_t *block = root;
    size_t size_fit = (size_t)-1;
    int num_checked = 200;

    while (block != NULL && num_checked > 0)
    {
        size_t blockSize = get_size(block);

        // Check for a perfect fit
        if (blockSize == asize)
        {
            return block;
        }

        // If this block is a better fit, update best_fit_block and size_fit
        if (asize <= blockSize)
        {
            if (blockSize < size_fit)
            {
                size_fit = blockSize;
                best_fit_block = block;
            }
        }

        block = block->next; // Move to the next block
        num_checked--;       // Decrement the num_checked
    }

    return best_fit_block;
    // Return the best_fit_block fitting block or
    // NULL if no fitting block was found
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n - 1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 *          and theseond lowest bit reflects allocation status of previous block
 */
static word_t pack(size_t size, bool alloc, bool alloc_of_prev)
{
    return (size | (alloc ? 1 : 0) | (alloc_of_prev ? 2 : 0));
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & ~(word_t)0xF);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */

static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & 0x1);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc, bool alloc_of_prev)
{
    block->header = pack(size, alloc, alloc_of_prev);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc, false);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    return (block_t *)(((char *)block) + get_size(block));
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

// setting allocation status of previous block
static void prev_make(block_t *block, bool al_prev)
{
    if (al_prev)
        block->header = block->header | 0x2;
    else
    {
        block->header = block->header & (~(word_t)(0x2));
    }
}

// getting allocation status of previous block
bool get_alloc_of_prev(block_t *block)
{
    return (bool)((block->header) & 0x2);
}

// Verifies the epilogue and prologue block's size and allocation status.
bool check_block(block_t *block)
{
    return extract_size(block->header) == 0 && get_alloc(block) == 1;
}

// Checks for no consecutive free blocks in the heap.
bool check_adj_free_blocks(block_t *current_blk)
{
    bool prev_free = false;
    while (get_size(current_blk) > 0)
    {
        bool curr_alloc = get_alloc(current_blk);
        if (!curr_alloc && prev_free)
            return false;
        prev_free = !curr_alloc;
        current_blk = find_next(current_blk);
    }
    return true;
}


// Checks for proper block alignment and minimum block size.
bool check_alignment_min_size(block_t *current_blk)
{
    size_t blk_address = (size_t)current_blk - wsize;
    size_t blk_size = extract_size(current_blk->header);
    return (blk_address % dsize == 0) && (blk_size >= min_block_size);
}

// Verifies that the block resides within the boundaries of the heap.
bool check_within_heap(block_t *current_blk)
{
    return ((current_blk <= (block_t *)mem_heap_hi() && (block_t *)mem_heap_lo() <= current_blk));
}

// Validates the free list's consistency and pointer ranges.
bool check_free_list(block_t *start_free_blk, uint64_t count_expected)
{
    uint64_t free_list_count = 0;
    for (block_t *current = start_free_blk; current != NULL; current = current->next)
    {
        // Increase free block count
        free_list_count++;
        // Check if next and previous blocks are within heap boundaries
        if ((current->next && !check_within_heap(current->next)) ||
            (current->prev && !check_within_heap(current->prev)))
        {
            return false;
        }
    }
    // Check if counted free blocks match the expected number
    return free_list_count == count_expected;
}

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int line_number)
{
    block_t *start_blk = (block_t *)mem_heap_lo();
    block_t *end_blk = (block_t *)((char *)mem_heap_hi() - 7);
    if (!(check_block(end_blk) && check_block(start_blk)))
        return false;

    uint64_t free_blk_count = 0;

    // Iterates through each block in the heap to perform various checks.
    for (block_t *current_blk = heap_listp; get_size(current_blk) > 0; current_blk = find_next(current_blk))
    {
        // check for proper coalescing
        if (!check_adj_free_blocks(current_blk))
        {
            return false;
        }

        // Ensures each block is within the heap bounds
        if (!check_within_heap(current_blk))
            return false;

        // Checks alignment and minimum size requirements for each block.
        if (!check_alignment_min_size(current_blk))
            return false;

        // Increments the count of free blocks
        if (!get_alloc(current_blk))
            free_blk_count++;
    }

    // Verifies the free list count and pointer validity
    if (!check_free_list(root, free_blk_count))
        return false;

    // All checks passed
    return true;
}
