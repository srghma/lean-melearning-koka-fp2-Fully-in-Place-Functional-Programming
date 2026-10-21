#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>

typedef struct {
    char name[32];
    double score;
} Player;

/*
 * 64-Bit Memory Layout:
 *
 * Case 1: Immediate Integer (Tag bit 0 == 1)
 * [ 63-bit signed integer payload                          | 1 ]
 *
 * Case 2: Heap Pointer + 16-bit Extra Payload (Tag bit 0 == 0)
 * [ 16-bit Metadata Payload ] [ 47-bit Real Pointer Address | 0 ]
 */

typedef uintptr_t Value;

#define TAG_MASK        ((uintptr_t)0x1)
#define TAG_PTR         ((uintptr_t)0x0)
#define TAG_INT         ((uintptr_t)0x1)

/* Virtual addresses on 64-bit OSes occupy bits 0..47 */
#define PTR_MASK        ((uintptr_t)0x0000FFFFFFFFFFFFULL)
#define META_SHIFT      48

/* --- Constructors --- */

/* Store a massive 63-bit signed integer directly in the pointer */
static inline Value make_int(int64_t n) {
    return ((uintptr_t)n << 1) | TAG_INT;
}

/* Store a heap pointer + an extra 16-bit metadata integer in the same word */
static inline Value make_player_ptr(Player *p, uint16_t metadata) {
    uintptr_t raw = (uintptr_t)p;
    /* User-space pointer must fit within 48-bit canonical address */
    return (raw & PTR_MASK) | ((uintptr_t)metadata << META_SHIFT) | TAG_PTR;
}

/* --- Type Checking --- */

static inline bool is_int(Value v) {
    return (v & TAG_MASK) == TAG_INT;
}

static inline bool is_player_ptr(Value v) {
    return (v & TAG_MASK) == TAG_PTR;
}

/* --- Extractors --- */

/* Recovers the 63-bit signed integer with sign-extension */
static inline int64_t get_int(Value v) {
    return (int64_t)v >> 1;
}

/* Strips off the upper 16-bit metadata to recover the canonical pointer */
static inline Player* get_player_ptr(Value v) {
    return (Player *)(v & PTR_MASK);
}

/* Extracts the 16-bit metadata without dereferencing */
static inline uint16_t get_metadata(Value v) {
    return (uint16_t)(v >> META_SHIFT);
}

/* --- Demo --- */

void print_value(Value v) {
    if (is_int(v)) {
        printf("Immediate 63-bit Int: %" PRId64 "\n", get_int(v));
    } else if (is_player_ptr(v)) {
        Player *p = get_player_ptr(v);
        uint16_t meta = get_metadata(v);
        printf("Player: '%s' (Score: %.1f) | Stored Metadata: 0x%04X (%u)\n",
               p->name, p->score, meta, meta);
    }
}

int main(void) {
    /* 1. Store a massive number directly in the pointer (No malloc!) */
    Value val1 = make_int(-4611686018427387903LL); // Large 63-bit negative value

    /* 2. Allocate the object */
    Player *hero = (Player *)malloc(sizeof(Player));
    snprintf(hero->name, sizeof(hero->name), "Alice");
    hero->score = 99.5;

    /* 3. Embed a 16-bit auxiliary payload (e.g., Player Level = 500) into the pointer */
    uint16_t player_level = 500;
    Value val2 = make_player_ptr(hero, player_level);

    /* Test inspection */
    print_value(val1);
    print_value(val2);

    /* Free the heap memory using the stripped pointer */
    free(get_player_ptr(val2));
    return 0;
}
