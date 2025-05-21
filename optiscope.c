/*
BSD 3-Clause License

Copyright (c) 2025, Louis F. Ashfield

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
   contributors may be used to endorse or promote products derived from
   this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

// Header inclusionnes
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#include "optiscope.h"

#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE // in case we use glibc
#endif

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Miscellaneous macros
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#define ARRAY_LENGTH(array) (sizeof(array) / sizeof((array)[0]))

#ifndef NDEBUG
#define CLEAR_MEMORY(object) memset((object), '\0', sizeof *(object))
#else
#define CLEAR_MEMORY(object) /* empty */
#endif

#define ITERATE_ONCE(finish, before, after)                                    \
    for (bool finish = (before, false); !finish; after, finish = true)

#define CAT_PRIMITIVE(a, b) a##b
#define CAT(a, b)           CAT_PRIMITIVE(a, b)

#define STRINGIFY_PRIMITIVE(...) #__VA_ARGS__
#define STRINGIFY(...)           STRINGIFY_PRIMITIVE(__VA_ARGS__)

// Compiler functionalitie detection
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#define STANDARD_C99_OR_HIGHER (__STDC_VERSION__ >= 199901L)
#define STANDARD_C11_OR_HIGHER (__STDC_VERSION__ >= 201112L)

#if !STANDARD_C99_OR_HIGHER
#error C99 or higher is required!
#endif

#if !defined(NDEBUG) && defined(__has_feature) // Clang
#if __has_feature(address_sanitizer)
#define COMPILER_ASAN_AVAILABLE
#endif
#elif !defined(NDEBUG) && defined(__SANITIZE_ADDRESS__) // GCC & MSVC
#define COMPILER_ASAN_AVAILABLE
#endif

#ifdef COMPILER_ASAN_AVAILABLE
#include <sanitizer/asan_interface.h>
#endif

#ifdef __GNUC__
#include <sys/mman.h>
#include <unistd.h>
#endif

// Perhaps for future use...
#if defined(_OPENMP) && defined(NDEBUG)
#include <omp.h>
#define MY_OPENMP(...) _Pragma(__VA_ARGS__)
#else
#define MY_OPENMP(...) /* empty */
#endif

// Compiler-specific builtins
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#ifdef __GNUC__

// We generally trust the compiler whether or not to inline a function.
// However, we utilize a number of other attributes, to help both the human
// reader & the compiler.
// See <https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html> for
// the list of GNU C function attributes.
// Note: please, keep `.clang-format` up-to-date with the macros below.

#define COMPILER_UNUSED             __attribute__((unused))
#define COMPILER_NORETURN           __attribute__((noreturn))
#define COMPILER_COLD               __attribute__((cold))
#define COMPILER_HOT                __attribute__((hot))
#define COMPILER_FLATTEN            __attribute__((flatten))
#define COMPILER_RETURNS_NONNULL    __attribute__((returns_nonnull))
#define COMPILER_WARN_UNUSED_RESULT __attribute__((warn_unused_result))
#define COMPILER_FALLTHROUGH        __attribute__((fallthrough))

#ifndef __clang__

#define COMPILER_MALLOC(deallocator, ptr_index)                                \
    __attribute__((malloc(deallocator, ptr_index)))

#endif // __clang__

#define COMPILER_FORMAT(archetype, string_index, first_to_check)               \
    __attribute__((format(archetype, string_index, first_to_check)))

#ifdef NDEBUG

#define COMPILER_UNREACHABLE() __builtin_unreachable()
#define COMPILER_NONNULL(...)  __attribute__((nonnull(__VA_ARGS__)))
#define COMPILER_CONST         __attribute__((const))
#define COMPILER_PURE          __attribute__((pure))

#else

#define COMPILER_UNREACHABLE() assert(false)
#define COMPILER_NONNULL(...)  /* checked by `assert` */
#define COMPILER_CONST         /* may invoke side-effecting `assert` */
#define COMPILER_PURE          /* may invoke side-effecting `assert` */

#endif // NDEBUG

#endif // __GNUC__

#ifdef COMPILER_ASAN_AVAILABLE
#define COMPILER_POISON_MEMORY       ASAN_POISON_MEMORY_REGION
#define COMPILER_UNPOISON_MEMORY     ASAN_UNPOISON_MEMORY_REGION
#define COMPILER_IS_POISONED_ADDRESS __asan_address_is_poisoned
#define COMPILER_IS_POISONED_MEMORY  __asan_region_is_poisoned
#endif

#define COMPILER_IGNORE                /* empty, object-like */
#define COMPILER_IGNORE_WITH_ARGS(...) /* empty, function-like */

#ifndef COMPILER_UNUSED
#define COMPILER_UNUSED COMPILER_IGNORE
#endif

#ifndef COMPILER_NORETURN
#if STANDARD_C11_OR_HIGHER
#define COMPILER_NORETURN _Noreturn
#else
#define COMPILER_NORETURN COMPILER_IGNORE
#endif
#endif

#ifndef COMPILER_COLD
#define COMPILER_COLD COMPILER_IGNORE
#endif

#ifndef COMPILER_HOT
#define COMPILER_HOT COMPILER_IGNORE
#endif

#ifndef COMPILER_FLATTEN
#define COMPILER_FLATTEN COMPILER_IGNORE
#endif

#ifndef COMPILER_RETURNS_NONNULL
#define COMPILER_RETURNS_NONNULL COMPILER_IGNORE
#endif

#ifndef COMPILER_WARN_UNUSED_RESULT
#define COMPILER_WARN_UNUSED_RESULT COMPILER_IGNORE
#endif

#ifndef COMPILER_FALLTHROUGH
#define COMPILER_FALLTHROUGH COMPILER_IGNORE
#endif

#ifndef COMPILER_MALLOC
#define COMPILER_MALLOC COMPILER_IGNORE_WITH_ARGS
#endif

#ifndef COMPILER_FORMAT
#define COMPILER_FORMAT COMPILER_IGNORE_WITH_ARGS
#endif

#ifndef COMPILER_UNREACHABLE
#define COMPILER_UNREACHABLE COMPILER_IGNORE_WITH_ARGS
#endif

#ifndef COMPILER_NONNULL
#define COMPILER_NONNULL COMPILER_IGNORE
#endif

#ifndef COMPILER_CONST
#define COMPILER_CONST COMPILER_IGNORE
#endif

#ifndef COMPILER_PURE
#define COMPILER_PURE COMPILER_IGNORE
#endif

#ifndef COMPILER_POISON_MEMORY
#define COMPILER_POISON_MEMORY COMPILER_IGNORE_WITH_ARGS
#endif

#ifndef COMPILER_UNPOISON_MEMORY
#define COMPILER_UNPOISON_MEMORY COMPILER_IGNORE_WITH_ARGS
#endif

#ifndef COMPILER_IS_POISONED_ADDRESS
#define COMPILER_IS_POISONED_ADDRESS COMPILER_IGNORE_WITH_ARGS
#endif

#ifndef COMPILER_IS_POISONED_MEMORY
#define COMPILER_IS_POISONED_MEMORY COMPILER_IGNORE_WITH_ARGS
#endif

// Debug assertionnes
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

// Assertionnes that are checked at program run-time.
#if defined(__GNUC__) && defined(NDEBUG)
#define XASSERT(condition) (!(condition) ? __builtin_unreachable() : (void)0)
#else
#define XASSERT assert
#endif

// Assertionnes that are checked at compile-time.
#if defined(__GNUC__) || STANDARD_C11_OR_HIGHER
#define STATIC_ASSERT _Static_assert
#else
// clang-format off
#define STATIC_ASSERT(constant_expression, string_literal) \
    COMPILER_UNUSED /* */ \
    static const char CAT(c99_static_assert_, __LINE__) \
        [(constant_expression) ? 1 : -1] = {0}
// clang-format on
#endif

// File-related I/O
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#define IO_CALL(f, ...) (f(__VA_ARGS__) < 0 ? (perror(#f), abort()) : (void)0)
#define IO_CALL_ASSIGN(x, f, ...)                                              \
    ((x = f(__VA_ARGS__)) < 0 ? (perror(#f), abort()) : (void)0)

extern void
optiscope_redirect_stream(
    FILE *const restrict source,
    FILE *const restrict destination) {
    assert(source);
    assert(destination);

    int c;
    while (EOF != (c = fgetc(source))) {
        if (EOF == fputc(c, destination)) { perror("fputc"), abort(); }
    }

    if (ferror(source) != 0) { perror("fgetc"), abort(); }
}

// Logging & panicking
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#define PRINTER(name, stream, culmination)                                     \
    COMPILER_NONNULL(1) COMPILER_FORMAT(printf, 1, 2) /* */                    \
    static void                                                                \
    name(const char format[const restrict], ...) {                             \
        assert(format);                                                        \
                                                                               \
        va_list args;                                                          \
        va_start(args, format);                                                \
        vfprintf(stream, format, args);                                        \
        fputs("\n", stream);                                                   \
        va_end(args);                                                          \
                                                                               \
        culmination;                                                           \
    }

#ifdef OPTISCOPE_ENABLE_TRACING
PRINTER(debug, stdout, /* empty */)
#else
#define debug(...) ((void)0)
#endif

COMPILER_COLD COMPILER_NORETURN //
PRINTER(panic, stderr, abort())

#undef PRINTER

// Ports & symbols functionalitie
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#define MACHINE_WORD_BITS    UINT64_C(64)
#define OFFSET_METADATA_BITS UINT64_C(2)
#define PHASE_METADATA_BITS  UINT64_C(2)
#define EFFECTIVE_ADDRESS_BITS                                                 \
    (MACHINE_WORD_BITS - OFFSET_METADATA_BITS - PHASE_METADATA_BITS)
#define UNUSED_ADDRESS_BITS (MACHINE_WORD_BITS - EFFECTIVE_ADDRESS_BITS)
#define ADDRESS_MASK        (~UINT64_C(0) >> UNUSED_ADDRESS_BITS)

#define ENCODE_METADATA(offset, phase)                                         \
    ((((offset) << PHASE_METADATA_BITS) | (phase)) << EFFECTIVE_ADDRESS_BITS)
#define DECODE_OFFSET_METADATA(address)                                        \
    ((address) >> (EFFECTIVE_ADDRESS_BITS + PHASE_METADATA_BITS))
#define DECODE_PHASE_METADATA(address)                                         \
    (((address) << OFFSET_METADATA_BITS) >>                                    \
     (EFFECTIVE_ADDRESS_BITS + PHASE_METADATA_BITS))

#define ENCODE_ADDRESS(metadata, address)                                      \
    (((address) & ADDRESS_MASK) | (metadata))
#define SIGN_EXTEND(n)                                                         \
    ((uint64_t)((int64_t)((n) << UNUSED_ADDRESS_BITS) >> UNUSED_ADDRESS_BITS))
#define DECODE_ADDRESS(address)                                                \
    ((uint64_t *)(SIGN_EXTEND((address) & ADDRESS_MASK)))
#define DECODE_ADDRESS_METADATA(address) (((address) & ~ADDRESS_MASK))

#define SET_PHASE(address, phase)                                              \
    (((address) & 0xCFFFFFFFFFFFFFFF) |                                        \
     ENCODE_METADATA(UINT64_C(0) /* the principal port */, (phase)))

STATIC_ASSERT(CHAR_BIT == 8, "The byte width must be 8 bits!");
STATIC_ASSERT(
    sizeof(uint64_t *) == sizeof(uint64_t),
    "The machine word width must be 64 bits!");
STATIC_ASSERT(
    sizeof(uint64_t (*)(uint64_t value)) <= sizeof(uint64_t),
    "Function handles must fit in `uint64_t`!");

#define MIN_REGULAR_SYMBOL   UINT64_C(0)
#define MAX_REGULAR_SYMBOL   UINT64_C(7)
#define INDEX_RANGE          UINT64_C(9223372036854775804)
#define MAX_DUPLICATOR_INDEX (MAX_REGULAR_SYMBOL + INDEX_RANGE)
#define MAX_DELIMITER_INDEX  (MAX_DUPLICATOR_INDEX + INDEX_RANGE)
#define MAX_PORTS            UINT64_C(3)
#define MAX_AUXILIARY_PORTS  (MAX_PORTS - 1)

STATIC_ASSERT(
    UINT64_MAX == UINT64_C(18446744073709551615),
    "`uint64_t` must have the expected range of [0; 2^64 - 1]!");
STATIC_ASSERT(
    UINT64_MAX == MAX_DELIMITER_INDEX,
    "Every bit of a symbol must be used!");

#define IS_PRINCIPAL_PORT(port) (0 == DECODE_OFFSET_METADATA(port))

#define SYMBOL_ROOT          UINT64_C(0)
#define SYMBOL_GARBAGE       UINT64_C(1)
#define SYMBOL_APPLICATOR    UINT64_C(2)
#define SYMBOL_LAMBDA        UINT64_C(3)
#define SYMBOL_ERASER        UINT64_C(4)
#define SYMBOL_S             UINT64_C(5)
#define SYMBOL_CELL          UINT64_C(6)
#define SYMBOL_INVOKE        UINT64_C(7)
#define SYMBOL_DUPLICATOR(i) (MAX_REGULAR_SYMBOL + 1 + (i))
#define SYMBOL_DELIMITER(i)  (MAX_DUPLICATOR_INDEX + 1 + (i))

// clang-format off
#define IS_DUPLICATOR(symbol) \
    ((symbol) >= SYMBOL_DUPLICATOR(UINT64_C(0)) && \
     (symbol) <= MAX_DUPLICATOR_INDEX)
#define IS_DELIMITER(symbol) \
    ((symbol) >= SYMBOL_DELIMITER(UINT64_C(0)))
// clang-format on

struct symbol_range {
    uint64_t min, max;
};

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT COMPILER_HOT //
inline static bool
symbol_is_in_range(const struct symbol_range range, const uint64_t symbol) {
    return range.min <= symbol && symbol <= range.max;
}

// clang-format off
#define SYMBOL_RANGE(min, max) ((struct symbol_range){min, max})
#define SYMBOL_RANGE_1(symbol) SYMBOL_RANGE(symbol, symbol)
#define DUPLICATOR_RANGE \
    SYMBOL_RANGE(SYMBOL_DUPLICATOR(UINT64_C(0)), MAX_DUPLICATOR_INDEX)
#define DELIMITER_RANGE \
    SYMBOL_RANGE(SYMBOL_DELIMITER(UINT64_C(0)), MAX_DELIMITER_INDEX)
// clang-format on

#define FOR_ALL_PORTS(node, i, seed)                                           \
    for (uint8_t i = seed; i < ports_count((node).ports[-1]); i++)

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT COMPILER_HOT //
static uint8_t
ports_count(const uint64_t symbol) {
    switch (symbol) {
    case SYMBOL_ROOT: return 2;
    case SYMBOL_APPLICATOR:
    case SYMBOL_LAMBDA: return 3;
    case SYMBOL_ERASER: return 1;
    case SYMBOL_S: return 2;
    case SYMBOL_CELL: return 1;
    case SYMBOL_INVOKE: return 2;
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        return 3;
    delimiter:
        return 2;
    }
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_RETURNS_NONNULL
COMPILER_NONNULL(1) //
inline static uint64_t *
get_principal_port(uint64_t *const restrict port) {
    assert(port);

    return (port - DECODE_OFFSET_METADATA(port[0]));
}

COMPILER_NONNULL(1, 2) COMPILER_HOT //
static void
connect_port_to(
    uint64_t *const restrict port,
    const uint64_t *const restrict another) {
    assert(port);
    assert(another);
    XASSERT(port != another);
    XASSERT(DECODE_ADDRESS(*port) != another);

    const uint64_t port_metadata = DECODE_ADDRESS_METADATA(*port);

    *port = ENCODE_ADDRESS(port_metadata, (uint64_t)another);

    XASSERT(DECODE_ADDRESS(*port) == another);
    XASSERT(DECODE_ADDRESS_METADATA(*port) == port_metadata);
}

COMPILER_NONNULL(1, 2) COMPILER_HOT COMPILER_FLATTEN //
static void
connect_ports(uint64_t *const restrict lhs, uint64_t *const restrict rhs) {
    debug("%s(%p, %p)", __func__, (void *)lhs, (void *)rhs);

    // Delegate the assertionnes to `connect_ports_to`.
    assert(true);

    connect_port_to(lhs, rhs), connect_port_to(rhs, lhs);
}

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT COMPILER_HOT //
static int64_t
symbol_index(const uint64_t symbol) {
    STATIC_ASSERT(
        INDEX_RANGE <= (uint64_t)INT64_MAX, "Indices must fit in `int64_t`!");

    switch (symbol) {
    case SYMBOL_ROOT:
    case SYMBOL_GARBAGE:
    case SYMBOL_APPLICATOR:
    case SYMBOL_LAMBDA:
    case SYMBOL_ERASER:
    case SYMBOL_S:
    case SYMBOL_CELL:
    case SYMBOL_INVOKE: return -1;
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        return (int64_t)(symbol - MAX_REGULAR_SYMBOL - 1);
    delimiter:
        return (int64_t)(symbol - MAX_DUPLICATOR_INDEX - 1);
    }
}

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT //
inline static bool
is_canonical_symbol(const uint64_t symbol) {
    if (IS_DUPLICATOR(symbol) || IS_DELIMITER(symbol)) {
        return 0 == symbol_index(symbol);
    }

    return true;
}

#define MAX_SSYMBOL_SIZE 64

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT COMPILER_RETURNS_NONNULL //
static const char *
print_symbol(const uint64_t symbol) {
    static char buffer[MAX_SSYMBOL_SIZE] = {0};

    switch (symbol) {
    case SYMBOL_ROOT: sprintf(buffer, "root"); break;
    case SYMBOL_GARBAGE: sprintf(buffer, "garbage"); break;
    case SYMBOL_APPLICATOR: sprintf(buffer, "@"); break;
    case SYMBOL_LAMBDA: sprintf(buffer, "λ"); break;
    case SYMBOL_ERASER: sprintf(buffer, "◉"); break;
    case SYMBOL_S: sprintf(buffer, "S"); break;
    case SYMBOL_CELL: sprintf(buffer, "cell"); break;
    case SYMBOL_INVOKE: sprintf(buffer, "invoke"); break;
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        sprintf(buffer, "▽/%" PRIi64, symbol_index(symbol));
        break;
    delimiter:
        sprintf(buffer, "⌒/%" PRIi64, symbol_index(symbol));
        break;
    }

    return buffer;
}

COMPILER_WARN_UNUSED_RESULT //
static uint64_t
bump_index(const uint64_t symbol) {
    if (MAX_DELIMITER_INDEX == symbol || MAX_DUPLICATOR_INDEX == symbol) {
        panic("Maximum index of %" PRIu64 " is reached!", INDEX_RANGE);
    } else if (symbol > MAX_REGULAR_SYMBOL) {
        return symbol + 1;
    } else {
        panic(
            "The symbol `%s` has no index to bump!", //
            print_symbol(symbol));
    }
}

// O(1) pool allocation & deallocation
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_MALLOC(free, 1)
COMPILER_RETURNS_NONNULL COMPILER_WARN_UNUSED_RESULT //
static void *
xmalloc(const size_t size) {
    XASSERT(size > 0);

    void *const object = malloc(size);
    if (NULL == object) { panic("Failed allocation!"); }

    return object;
}

COMPILER_MALLOC(free, 1)
COMPILER_RETURNS_NONNULL COMPILER_WARN_UNUSED_RESULT //
static void *
xcalloc(const size_t n, const size_t size) {
    XASSERT(size > 0);

    void *const object = calloc(n, size);
    if (NULL == object) { panic("Failed allocation!"); }

    return object;
}

#define POOL_CHUNK_LIST_SIZE 1024 /* for all types of objects */

#define POOL_ALLOCATOR(prefix, chunk_size)                                     \
    union prefix##_chunk {                                                     \
        char data[chunk_size];                                                 \
        union prefix##_chunk *next;                                            \
    };                                                                         \
                                                                               \
    struct prefix##_chunks_bucket {                                            \
        union prefix##_chunk *chunks;                                          \
        struct prefix##_chunks_bucket *next;                                   \
    };                                                                         \
                                                                               \
    struct prefix##_pool {                                                     \
        union prefix##_chunk *next_free_chunk;                                 \
        struct prefix##_chunks_bucket *buckets;                                \
    };                                                                         \
                                                                               \
    COMPILER_NONNULL(1) COMPILER_COLD /* */                                    \
    static void prefix##_pool_close(                                           \
        struct prefix##_pool *const restrict self);                            \
                                                                               \
    COMPILER_MALLOC(prefix##_pool_close, 1)                                    \
    COMPILER_RETURNS_NONNULL COMPILER_WARN_UNUSED_RESULT COMPILER_COLD /* */   \
    static struct prefix##_pool *prefix##_pool_create(void) {                  \
        struct prefix##_pool *const self = xmalloc(sizeof *self);              \
                                                                               \
        union prefix##_chunk *chunks =                                         \
            xmalloc(POOL_CHUNK_LIST_SIZE * sizeof chunks[0]);                  \
        for (size_t i = 0; i < POOL_CHUNK_LIST_SIZE - 1; i++) {                \
            chunks[i].next = &chunks[i + 1];                                   \
        }                                                                      \
        chunks[POOL_CHUNK_LIST_SIZE - 1].next = NULL;                          \
        self->next_free_chunk = chunks;                                        \
                                                                               \
        struct prefix##_chunks_bucket *const buckets =                         \
            xmalloc(sizeof buckets[0]);                                        \
        buckets->chunks = chunks, buckets->next = NULL;                        \
        self->buckets = buckets;                                               \
                                                                               \
        return self;                                                           \
    }                                                                          \
                                                                               \
    COMPILER_NONNULL(1) COMPILER_COLD /* */                                    \
    static void prefix##_pool_close(                                           \
        struct prefix##_pool *const restrict self) {                           \
        assert(self);                                                          \
        XASSERT(self->buckets);                                                \
                                                                               \
        struct prefix##_chunks_bucket *iter = self->buckets;                   \
        while (iter) {                                                         \
            struct prefix##_chunks_bucket *next = iter->next;                  \
            XASSERT(iter->chunks);                                             \
            free(iter->chunks);                                                \
            free(iter);                                                        \
            iter = next;                                                       \
        }                                                                      \
                                                                               \
        free(self);                                                            \
    }                                                                          \
                                                                               \
    COMPILER_NONNULL(1) COMPILER_COLD /* */                                    \
    static void prefix##_pool_expand(                                          \
        struct prefix##_pool *const restrict self) {                           \
        assert(self);                                                          \
        XASSERT(self->buckets);                                                \
                                                                               \
        union prefix##_chunk *const extra_chunks =                             \
            xmalloc(POOL_CHUNK_LIST_SIZE * sizeof extra_chunks[0]);            \
        for (size_t i = 0; i < POOL_CHUNK_LIST_SIZE - 1; i++) {                \
            extra_chunks[i].next = &extra_chunks[i + 1];                       \
        }                                                                      \
        extra_chunks[POOL_CHUNK_LIST_SIZE - 1].next = self->next_free_chunk;   \
        self->next_free_chunk = extra_chunks;                                  \
                                                                               \
        struct prefix##_chunks_bucket *const buckets =                         \
            xmalloc(sizeof buckets[0]);                                        \
        buckets->chunks = extra_chunks, buckets->next = self->buckets;         \
        self->buckets = buckets;                                               \
    }                                                                          \
                                                                               \
    COMPILER_NONNULL(1, 2) COMPILER_HOT /* */                                  \
    static void prefix##_pool_free(                                            \
        struct prefix##_pool *const restrict self, uint64_t *restrict object); \
                                                                               \
    COMPILER_MALLOC(prefix##_pool_free, 1)                                     \
    COMPILER_RETURNS_NONNULL COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1)   \
    COMPILER_HOT /* */                                                         \
    static uint64_t *prefix##_pool_alloc(                                      \
        struct prefix##_pool *const restrict self) {                           \
        assert(self);                                                          \
        XASSERT(self->buckets);                                                \
                                                                               \
        if (NULL == self->next_free_chunk) { prefix##_pool_expand(self); }     \
        XASSERT(self->next_free_chunk);                                        \
                                                                               \
        COMPILER_UNPOISON_MEMORY(self->next_free_chunk, chunk_size);           \
        void *const object = (void *)self->next_free_chunk;                    \
        self->next_free_chunk = self->next_free_chunk->next;                   \
                                                                               \
        return (uint64_t *)object + 1 /* pass the symbol */;                   \
    }                                                                          \
                                                                               \
    COMPILER_NONNULL(1, 2) COMPILER_HOT /* */                                  \
    static void prefix##_pool_free(                                            \
        struct prefix##_pool *const restrict self,                             \
        uint64_t *restrict object) {                                           \
        assert(self);                                                          \
        XASSERT(self->buckets);                                                \
        assert(object);                                                        \
                                                                               \
        object--; /* back to the symbol address */                             \
        union prefix##_chunk *const freed = (union prefix##_chunk *)object;    \
        CLEAR_MEMORY(freed);                                                   \
        *object = SYMBOL_GARBAGE;                                              \
        freed->next = self->next_free_chunk;                                   \
        self->next_free_chunk = freed;                                         \
        COMPILER_POISON_MEMORY(freed, chunk_size);                             \
    }

POOL_ALLOCATOR(applicator, sizeof(uint64_t) * 4)
POOL_ALLOCATOR(lambda, sizeof(uint64_t) * 4)
POOL_ALLOCATOR(eraser, sizeof(uint64_t) * 2)
POOL_ALLOCATOR(scope, sizeof(uint64_t) * 3)
POOL_ALLOCATOR(duplicator, sizeof(uint64_t) * 4)
POOL_ALLOCATOR(delimiter, sizeof(uint64_t) * 3)
POOL_ALLOCATOR(cell, sizeof(uint64_t) * 3)
POOL_ALLOCATOR(invocation, sizeof(uint64_t) * 4)

#define POOLS                                                                  \
    X(applicator_pool)                                                         \
    X(lambda_pool)                                                             \
    X(eraser_pool)                                                             \
    X(scope_pool)                                                              \
    X(duplicator_pool)                                                         \
    X(delimiter_pool)                                                          \
    X(cell_pool)                                                               \
    X(invocation_pool)

// clang-format off

#define X(pool_name) static struct pool_name *pool_name = NULL;
POOLS
#undef X

#define X(pool_name) \
    { \
        XASSERT(NULL == pool_name); \
        pool_name = pool_name##_create(); \
        XASSERT(pool_name); \
    }

extern void optiscope_open_pools(void) { POOLS }

#undef X

#define X(pool_name) \
    { \
        XASSERT(pool_name); \
        pool_name##_close(pool_name); \
        pool_name = NULL; \
    }

extern void optiscope_close_pools(void) { POOLS }

#undef X

// clang-format on

#undef POOLS

#undef POOL_ALLOCATOR
#undef POOL_CHUNK_LIST_SIZE

// Nodes functionalitie
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

struct node {
    uint64_t *ports;
};

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1) COMPILER_HOT
COMPILER_FLATTEN //
inline static struct node
node_of_port(uint64_t *const restrict port) {
    assert(port);

    const struct node node = {get_principal_port(port)};
    XASSERT(node.ports);

    return node;
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1) COMPILER_HOT
COMPILER_FLATTEN //
inline static struct node
follow_port(uint64_t *const restrict port) {
    assert(port);

    return node_of_port(DECODE_ADDRESS(*port));
}

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT COMPILER_HOT //
inline static int
compare_node_ptrs(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    if ((intptr_t)f.ports < (intptr_t)g.ports) return -1;
    else if ((intptr_t)f.ports > (intptr_t)g.ports) return 1;
    else return 0;
}

#define CONNECT_NODE(node, ...)                                                \
    do {                                                                       \
        uint64_t *const ports[] = {__VA_ARGS__};                               \
        for (uint8_t i = 0; i < ARRAY_LENGTH(ports); i++) {                    \
            connect_ports(&node.ports[i], ports[i]);                           \
        }                                                                      \
    } while (0)

COMPILER_WARN_UNUSED_RESULT COMPILER_COLD //
inline static struct node
xmalloc_node(const uint64_t symbol, const uint64_t phase) {
    const uint64_t n = ports_count(symbol);

    uint64_t *ports = xmalloc(sizeof *ports * (n + 1));
    ports++;
    ports[-1] = symbol;

    for (uint64_t offset = 0; offset < n; offset++) {
        ports[offset] =
            ENCODE_ADDRESS(ENCODE_METADATA(offset, phase), UINT64_C(0));
    }

    return (struct node){ports};
}

#ifdef OPTISCOPE_ENABLE_TRACING

#define MAX_SNODE_SIZE 256

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT COMPILER_RETURNS_NONNULL //
static const char *
print_node(const struct node node) {
    XASSERT(node.ports);

    static char buffer[MAX_SNODE_SIZE] = {0};

    const uint64_t *const p = node.ports;
    const char *const ssymbol = print_symbol(p[-1]);

    switch (ports_count(p[-1])) {
    case 1: sprintf(buffer, "%s [%p]", ssymbol, (void *)&p[0]); break;
    case 2:
        sprintf(buffer, "%s [%p, %p]", ssymbol, (void *)&p[0], (void *)&p[1]);
        break;
    case 3:
        sprintf(
            buffer,
            "%s [%p, %p, %p]",
            ssymbol,
            (void *)&p[0],
            (void *)&p[1],
            (void *)&p[2]);
        break;
    default: COMPILER_UNREACHABLE();
    }

    return buffer;
}

#endif // OPTISCOPE_ENABLE_TRACING

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_HOT //
inline static bool
is_interaction(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    return DECODE_ADDRESS(f.ports[0]) == &g.ports[0] &&
           DECODE_ADDRESS(g.ports[0]) == &f.ports[0];
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_HOT //
inline static bool
is_interacting_with(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    // Supposing that `g` is derived from `f` by `follow_port(&f.ports[0])`.
    return DECODE_ADDRESS(g.ports[0]) == &f.ports[0];
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT //
inline static bool
is_active(const struct node node) {
    XASSERT(node.ports);

    return is_interacting_with(node, follow_port(&node.ports[0]));
}

// clang-format off
COMPILER_HOT static void free_node(const struct node node);
// clang-format on

COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1) COMPILER_HOT //
inline static bool
is_garbage_node(uint64_t *const restrict port) {
    assert(port);

#ifdef COMPILER_ASAN_AVAILABLE
    return COMPILER_IS_POISONED_ADDRESS(port);
#else
    return SYMBOL_GARBAGE == *(get_principal_port(port) - 1);
#endif
}

COMPILER_HOT //
static void
free_node_if_non_active(const struct node f) {
    XASSERT(f.ports);

    if (is_garbage_node(f.ports)) { return; }

    uint64_t *const target_port = DECODE_ADDRESS(f.ports[0]);
    if (is_garbage_node(target_port)) { return; }

    const struct node g = node_of_port(target_port);

    if (is_interacting_with(f, g)) { return; }

    free_node(f);
}

// A linked list of nodes
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

struct node_list {
    struct node node;
    struct node_list *cons;
};

#define ITERATE_LIST(iter, seed)                                               \
    for (struct node_list *iter = seed; iter; iter = iter->cons)

#define CONSUME_LIST(iter, seed)                                               \
    for (struct node_list *iter = seed, *cons = NULL; iter;                    \
         cons = iter->cons, (free(iter), iter = cons))

COMPILER_WARN_UNUSED_RESULT COMPILER_RETURNS_NONNULL //
static struct node_list *
visit(struct node_list *const restrict self, const struct node node) {
    XASSERT(node.ports);

    struct node_list *const cons = xmalloc(sizeof *cons);
    cons->node = node;
    cons->cons = self;

    return cons;
}

COMPILER_NONNULL(1) //
static struct node
unvisit(struct node_list **const restrict self) {
    assert(self);
    XASSERT(*self);

    const struct node node = (*self)->node;
    struct node_list *const cons = (*self)->cons;

    free(*self), *self = cons;

    return node;
}

#ifdef OPTISCOPE_ENABLE_GRAPHVIZ

COMPILER_WARN_UNUSED_RESULT //
static struct node_list *
unvisit_all(struct node_list *const restrict self) {
    CONSUME_LIST (iter, self) {}
    return NULL;
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT //
static bool
is_visited(
    const struct node_list *const restrict self,
    const struct node node) {
    XASSERT(node.ports);

    ITERATE_LIST (iter, (struct node_list *)self) {
        if (iter->node.ports == node.ports) { return true; }
    }

    return false;
}

#define GUARD_NODE(history, node /* parameter */)                              \
    do {                                                                       \
        if (is_visited((history), node)) { return; }                           \
        (history) = visit((history), node);                                    \
    } while (false)

#endif // OPTISCOPE_ENABLE_GRAPHVIZ

// Graphs (nets) of nodes
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#ifndef OPTISCOPE_MULTIFOCUS_COUNT
#define OPTISCOPE_MULTIFOCUS_COUNT (1024 * 1024)
#endif

struct multifocus {
    size_t count;
    struct node initial[OPTISCOPE_MULTIFOCUS_COUNT];
    struct node_list *fallback;
};

COMPILER_NONNULL(1) COMPILER_HOT COMPILER_FLATTEN //
static void
focus_on(struct multifocus *const restrict focus, const struct node node) {
    assert(focus);
    XASSERT(node.ports);

    if (SIZE_MAX == focus->count) { panic("The focus is full!"); }

    if (focus->count < ARRAY_LENGTH(focus->initial)) {
        focus->initial[focus->count] = node;
    } else {
        focus->fallback = visit(focus->fallback, node);
    }

    focus->count++;
}

COMPILER_NONNULL(1) COMPILER_HOT COMPILER_FLATTEN //
static struct node
unfocus(struct multifocus *const restrict focus) {
    assert(focus);
    XASSERT(focus->count > 0);

    focus->count--;
    return focus->count < ARRAY_LENGTH(focus->initial)
               ? focus->initial[focus->count]
               : unvisit(&focus->fallback);
}

#define CONSUME_FOCUS(focus, f)                                                \
    for (struct node f = (focus)->initial[0]; (focus)->count > 0;              \
         f = unfocus(focus))

struct node_graph {
    const struct node root;
    struct multifocus *annihilations, *commutations, *betas, *invocations;
    uint64_t current_phase;
    bool is_reading_back;

#ifdef OPTISCOPE_ENABLE_STATS
    uint64_t nannihilations, ncommutations, nbetas, ninvocations;
#endif
};

COMPILER_PURE COMPILER_NONNULL(1) COMPILER_HOT //
inline static bool
is_normalized_graph(const struct node_graph *const restrict graph) {
    assert(graph);

    return 0 == graph->betas->count &&         //
           0 == graph->annihilations->count && //
           0 == graph->commutations->count &&  //
           0 == graph->invocations->count;
}

COMPILER_NONNULL(1) COMPILER_COLD //
static void
free_graph(struct node_graph *const restrict graph) {
    debug("%s()", __func__);

    assert(graph);
    XASSERT(graph->root.ports);
    XASSERT(graph->annihilations), XASSERT(0 == graph->annihilations->count);
    XASSERT(graph->commutations), XASSERT(0 == graph->commutations->count);
    XASSERT(graph->betas), XASSERT(0 == graph->betas->count);
    XASSERT(graph->invocations), XASSERT(0 == graph->invocations->count);
    XASSERT(!graph->is_reading_back);

    free(DECODE_ADDRESS(graph->root.ports[0]) - 1 /* back to the symbol */);
    free(graph->root.ports - 1 /* back to the symbol */);

    free(graph->annihilations);
    free(graph->commutations);
    free(graph->betas);
    free(graph->invocations);
}

COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1) COMPILER_HOT //
static struct node
alloc_node(struct node_graph *const restrict graph, const uint64_t symbol) {
    assert(graph);
    XASSERT(SYMBOL_ROOT != symbol);

    // While it might seem that preallocation caches can increase performance,
    // in fact, they introduced almost a 2x slowdown.

    uint64_t *ports = NULL;
    switch (symbol) {
    case SYMBOL_APPLICATOR:
        ports = applicator_pool_alloc(applicator_pool);
        goto assign_port_2;
    case SYMBOL_LAMBDA:
        ports = lambda_pool_alloc(lambda_pool);
        goto assign_port_2;
    case SYMBOL_ERASER:
        ports = eraser_pool_alloc(eraser_pool);
        goto assign_port_0;
    case SYMBOL_S:
        ports = scope_pool_alloc(scope_pool); //
        goto assign_port_1;
    case SYMBOL_CELL:
        ports = cell_pool_alloc(cell_pool); //
        goto assign_port_0;
    case SYMBOL_INVOKE:
        ports = invocation_pool_alloc(invocation_pool);
        goto assign_port_2;
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        ports = duplicator_pool_alloc(duplicator_pool);
        goto assign_port_2;
    delimiter:
        ports = delimiter_pool_alloc(delimiter_pool);
        goto assign_port_1;
    }

    COMPILER_UNREACHABLE();

#define PORT_VALUE(offset)                                                     \
    ENCODE_ADDRESS(                                                            \
        ENCODE_METADATA(UINT64_C(offset), PHASE_VALUE(offset)), UINT64_C(0))
#define PHASE_VALUE(offset)                                                    \
    (0 == (offset) ? graph->current_phase /* the principal port */             \
                   : UINT64_C(0) /* a non-principal port */)

    // clang-format off
assign_port_2: ports[2] = PORT_VALUE(2);
assign_port_1: ports[1] = PORT_VALUE(1);
assign_port_0: ports[0] = PORT_VALUE(0);
    // clang-format on

#undef PHASE_VALUE
#undef PORT_VALUE

    ports[-1] = symbol;

    debug("%s(%s)", __func__, print_node((struct node){ports}));

    return (struct node){ports};
}

// clang-format off
#ifdef OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS
static void clear_graphviz_cluster_node(const struct node node);
#endif
// clang-format on

COMPILER_HOT //
static void
free_node(const struct node node) {
    debug("%s(%p)", __func__, (void *)node.ports);

    XASSERT(node.ports);

    const uint64_t symbol = node.ports[-1];
    XASSERT(SYMBOL_ROOT != symbol);
    XASSERT(SYMBOL_GARBAGE != symbol);

#ifdef OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS
    clear_graphviz_cluster_node(node);
#endif

    uint64_t *const p = node.ports;

#ifdef COMPILER_ASAN_AVAILABLE
    {
        const size_t region_size = sizeof *p * (ports_count(symbol) + 1);

        if (COMPILER_IS_POISONED_MEMORY(p - 1, region_size)) {
            // Invoke AddressSanitizer's use-after-poison report.
            memset(p - 1, '\0', region_size);
        }
    }
#endif

    switch (symbol) {
    case SYMBOL_APPLICATOR: applicator_pool_free(applicator_pool, p); break;
    case SYMBOL_LAMBDA: lambda_pool_free(lambda_pool, p); break;
    case SYMBOL_ERASER: eraser_pool_free(eraser_pool, p); break;
    case SYMBOL_S: scope_pool_free(scope_pool, p); break;
    case SYMBOL_CELL: cell_pool_free(cell_pool, p); break;
    case SYMBOL_INVOKE: invocation_pool_free(invocation_pool, p); break;
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        duplicator_pool_free(duplicator_pool, p);
        break;
    delimiter:
        delimiter_pool_free(delimiter_pool, p);
        break;
    }
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
register_active_pair(
    struct node_graph *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);
    assert(is_interaction(f, g));

    const uint64_t f_symbol = f.ports[-1], g_symbol = g.ports[-1];

    if (f_symbol == SYMBOL_APPLICATOR && g_symbol == SYMBOL_LAMBDA) {
        focus_on(graph->betas, f);
    } else if (g_symbol == SYMBOL_APPLICATOR && f_symbol == SYMBOL_LAMBDA) {
        focus_on(graph->betas, g);
    } else if (f_symbol == SYMBOL_INVOKE && g_symbol == SYMBOL_CELL) {
        focus_on(graph->invocations, f);
    } else if (g_symbol == SYMBOL_INVOKE && f_symbol == SYMBOL_CELL) {
        focus_on(graph->invocations, g);
    } else if (f_symbol == g_symbol) {
        focus_on(graph->annihilations, f);
    } else {
        focus_on(graph->commutations, f);
    }
}

COMPILER_NONNULL(1) COMPILER_HOT //
inline static void
register_pair_if_active(
    struct node_graph *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);

    if (is_interaction(f, g)) { register_active_pair(graph, f, g); }
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
register_node_if_active(
    struct node_graph *const restrict graph,
    const struct node node) {
    assert(graph);
    XASSERT(node.ports);

    const struct node f = node, g = follow_port(&node.ports[0]);

    if (DECODE_ADDRESS(g.ports[0]) != &f.ports[0]) { return; }

    register_active_pair(graph, f, g);
}

// Graphviz graph generation
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#ifdef OPTISCOPE_ENABLE_GRAPHVIZ

// We use glibc-specific functionalitie for convenience. Windows support is not
// & will never be planned.
STATIC_ASSERT(__GNUC__ >= 1, "GNU C is required!");

#define GRAPHVIZ_INDENT             "    "
#define GRAPHVIZ_INDENT_2X          GRAPHVIZ_INDENT GRAPHVIZ_INDENT
#define GRAPHVIZ_ADDRESS_WIDTH_LINE "+----------------+"
#define GRAPHVIZ_ACTIVE_COLOR       "darkgreen"
#define GRAPHVIZ_STYLE_PLACEHOLDER  "// xxxxxxxxx"
#define GRAPHVIZ_HIDE               "style=invis;"

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_RETURNS_NONNULL //
static const char *
graphviz_node_xlabel(const struct node node) {
    XASSERT(node.ports);

    static char buffer[256] = {0};

    const uint64_t *const p = node.ports;

    switch (ports_count(p[-1])) {
    case 1:
        sprintf(
            buffer,
            GRAPHVIZ_ADDRESS_WIDTH_LINE "<BR/>| %p |<BR/>" //
            GRAPHVIZ_ADDRESS_WIDTH_LINE,
            (void *)&p[0]);
        break;
    case 2:
        sprintf(
            buffer,
            GRAPHVIZ_ADDRESS_WIDTH_LINE "<BR/>| %p |<BR/>| %p |<BR/>" //
            GRAPHVIZ_ADDRESS_WIDTH_LINE,
            (void *)&p[0],
            (void *)&p[1]);
        break;
    case 3:
        sprintf(
            buffer,
            GRAPHVIZ_ADDRESS_WIDTH_LINE
            "<BR/>| %p |<BR/>| %p |<BR/>| %p |<BR/>" //
            GRAPHVIZ_ADDRESS_WIDTH_LINE,
            (void *)&p[0],
            (void *)&p[1],
            (void *)&p[2]);
        break;
    default: COMPILER_UNREACHABLE();
    }

    return buffer;
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_RETURNS_NONNULL //
static const char *
graphviz_edge_label(
    const struct node node,
    const uint8_t i,
    const bool is_reading_back) {
    XASSERT(node.ports);

    static char buffer[16] = {0};

    switch (node.ports[-1]) {
    case SYMBOL_APPLICATOR:
        if ((is_reading_back ? 0 : 1) == i) {
            sprintf(buffer, "\\#%" PRIu8, i);
        } else if ((is_reading_back ? 2 : 0) == i) {
            sprintf(buffer, "rator (\\#%" PRIu8 ")", i);
        } else if ((is_reading_back ? 1 : 2) == i) {
            sprintf(buffer, "rand (\\#%" PRIu8 ")", i);
        } else {
            COMPILER_UNREACHABLE();
        }
        break;
    case SYMBOL_LAMBDA:
        switch (i) {
        case 0: sprintf(buffer, "\\#%" PRIu8, i); break;
        case 1: sprintf(buffer, "binder (\\#%" PRIu8 ")", i); break;
        case 2: sprintf(buffer, "body (\\#%" PRIu8 ")", i); break;
        default: COMPILER_UNREACHABLE();
        }
        break;
    default: sprintf(buffer, "\\#%" PRIu8, i);
    }

    return buffer;
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT //
static uint8_t
graphviz_edge_weight(
    const struct node node,
    const uint8_t i,
    const bool is_reading_back) {
    if (is_active(node) && 0 == i) { return 3; }

    switch (node.ports[-1]) {
    case SYMBOL_APPLICATOR:
        if ((is_reading_back ? 2 : 0) == i) {
            return 5; // rator
        }
        if ((is_reading_back ? 1 : 2) == i) {
            return 5; // rand
        }
        break;
    case SYMBOL_LAMBDA:
        if (2 == i) {
            return 3; // body
        }
        break;
    default:
        if (IS_DUPLICATOR(node.ports[-1]) && (1 == i || 2 == i)) {
            return 5; // the auxiliary ports
        }
    }

    // The Graphviz default value.
    return 1;
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_RETURNS_NONNULL //
static const char *
graphviz_edge_tailport(
    const struct node node,
    const uint8_t i,
    const bool is_reading_back) {
    XASSERT(node.ports);

    const uint64_t symbol = node.ports[-1];

    switch (symbol) {
    case SYMBOL_ROOT:
        switch (i) {
        case 0: return "n";
        case 1: return "s";
        default: COMPILER_UNREACHABLE();
        }
    case SYMBOL_APPLICATOR:
        if ((is_reading_back ? 0 : 1) == i) {
            return "n";
        } else if ((is_reading_back ? 2 : 0) == i) {
            return "s";
        } else if ((is_reading_back ? 1 : 2) == i) {
            return "e";
        } else {
            COMPILER_UNREACHABLE();
        }
    case SYMBOL_LAMBDA:
        switch (i) {
        case 0: return "n";
        case 1: return "e";
        case 2: return "s";
        default: COMPILER_UNREACHABLE();
        }
    case SYMBOL_ERASER:
    case SYMBOL_CELL:
        switch (i) {
        case 0: return "s";
        default: COMPILER_UNREACHABLE();
        }
    case SYMBOL_S:
        switch (i) {
        case 0: return "n";
        case 1: return "s";
        default: COMPILER_UNREACHABLE();
        }
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        switch (i) {
        case 0: return "s";
        case 1: return "nw";
        case 2: return "ne";
        default: COMPILER_UNREACHABLE();
        }
    delimiter:
    case SYMBOL_INVOKE:
        switch (i) {
        case 0: return "s";
        case 1: return "n";
        default: COMPILER_UNREACHABLE();
        }
    }
}

#ifdef OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS

#define GRAPHVIZ_BEGIN_CLUSTER "// begin cluster"
#define GRAPHVIZ_END_CLUSTER   "// end cluster"

// See <https://graphviz.org/Gallery/directed/cluster.html>.
static FILE *graphviz_footer_fp = NULL;

static uint16_t
graphviz_cluster_counter(void) {
    static uint16_t counter = 0;

    if (UINT16_MAX == counter) { panic("Graphviz cluster counter overflow!"); }
    return counter++;
}

COMPILER_NONNULL(1, 2) //
static void
graphviz_commute_cluster(
    const struct node f_updates[const restrict],
    const struct node g_updates[const restrict],
    const uint8_t m,
    const uint8_t n) {
    assert(f_updates), assert(g_updates);

    char connections[1024] = {0}, top_ranks[256] = {0}, bottom_ranks[256] = {0};

    // Initialize the (invisible) connectionnes between the nodes.
    for (uint8_t i = 0; i < m; i++) {
        for (uint8_t j = 0; j < n; j++) {
            const void *const ports[] = {
                (void *)f_updates[i].ports, (void *)g_updates[j].ports};

            for (uint8_t k = 0; k < ARRAY_LENGTH(ports); k++) {
                sprintf(
                    connections + strlen(connections),
                    GRAPHVIZ_INDENT_2X "n%p -> n%p [style=invis];\n",
                    ports[k],
                    ports[(k + 1) % ARRAY_LENGTH(ports)]);
            }
        }
    }

    // Initialize the top & bottom node ranks.
    for (uint8_t i = 0; i < m; i++) {
        sprintf(
            top_ranks + strlen(top_ranks), "; n%p", (void *)f_updates[i].ports);
    }
    for (uint8_t i = 0; i < n; i++) {
        sprintf(
            bottom_ranks + strlen(bottom_ranks),
            "; n%p",
            (void *)g_updates[i].ports);
    }

    // clang-format off
    fprintf(
        graphviz_footer_fp,
        "\n" GRAPHVIZ_INDENT "subgraph cluster_%" PRIu16 " {\n"
        GRAPHVIZ_INDENT_2X GRAPHVIZ_BEGIN_CLUSTER "\n"
                         /* style=invis; */
        GRAPHVIZ_INDENT_2X GRAPHVIZ_STYLE_PLACEHOLDER "\n"
        GRAPHVIZ_INDENT_2X "label=\"commute\";\n"
        GRAPHVIZ_INDENT_2X "color=darkblue;\n"
        GRAPHVIZ_INDENT_2X "margin=16;\n"
        "%s" // node connectionnes
        GRAPHVIZ_INDENT_2X "{rank=same%s}\n"
        GRAPHVIZ_INDENT_2X "{rank=same%s}\n"
        GRAPHVIZ_INDENT_2X GRAPHVIZ_END_CLUSTER "\n"
        GRAPHVIZ_INDENT "}\n",
        graphviz_cluster_counter(),
        connections,
        top_ranks,
        bottom_ranks);
    // clang-format on
}

COMPILER_NONNULL(1, 2) //
static void
graphviz_beta_cluster(
    const uint64_t *const restrict lhs,
    const uint64_t *const restrict rhs) {
    assert(lhs), assert(rhs);

    // clang-format off
    fprintf(
        graphviz_footer_fp,
        "\n" GRAPHVIZ_INDENT "subgraph cluster_%" PRIu16 " {\n"
        GRAPHVIZ_INDENT_2X GRAPHVIZ_BEGIN_CLUSTER "\n"
                         /* style=invis; */
        GRAPHVIZ_INDENT_2X GRAPHVIZ_STYLE_PLACEHOLDER "\n"
        GRAPHVIZ_INDENT_2X "label=\"Beta\";\n"
        GRAPHVIZ_INDENT_2X "color=darkblue;\n"
        GRAPHVIZ_INDENT_2X "margin=16;\n"
        GRAPHVIZ_INDENT_2X "n%p -> n%p [style=invis];\n"
        GRAPHVIZ_INDENT_2X "{rank=same; n%p; n%p}\n"
        GRAPHVIZ_INDENT_2X GRAPHVIZ_END_CLUSTER "\n"
        GRAPHVIZ_INDENT "}\n",
        graphviz_cluster_counter(),
        (void *)lhs,
        (void *)rhs,
        (void *)lhs,
        (void *)rhs);
    // clang-format on
}

#define DEFINED_graphviz_commute_cluster graphviz_commute_cluster
#define DEFINED_graphviz_beta_cluster    graphviz_beta_cluster

COMPILER_NONNULL(1, 2) //
static void *
mmap_graphviz_footer(
    size_t *const restrict mmap_length,
    char *const restrict mmap_backup_char) {
    assert(mmap_length), assert(mmap_backup_char);

    IO_CALL(fflush, graphviz_footer_fp);

    long length = 0;
    IO_CALL_ASSIGN(length, ftell, graphviz_footer_fp);
    if (0 == length) { return NULL; }

    const int fd = fileno(graphviz_footer_fp);

    char *ptr =
        mmap(NULL, (size_t)length, MAP_PRIVATE, PROT_READ | PROT_WRITE, fd, 0);
    if (MAP_FAILED == ptr) { perror("mmap"), abort(); }

    *mmap_length = (size_t)length;
    *mmap_backup_char = ptr[length - 1];
    ptr[length - 1] = '\0';

    return (void *)ptr;
}

// Mark clusters consisting of onely invisible nodes invisible as well.
static void
postprocess_graphviz_footer(void) {
    char *ptr = NULL, *ptrx = NULL;
    size_t length = 0;
    char clast = '\0';
    ptr = ptrx = mmap_graphviz_footer(&length, &clast);
    if (NULL == ptr) { return; }

    while ((ptr = strstr(ptr, GRAPHVIZ_BEGIN_CLUSTER))) {
        char *const end = strstr(ptr, GRAPHVIZ_END_CLUSTER);
        XASSERT(end);

        const char backup_char = *end;
        *end = '\0';
        if (NULL != strstr(ptr, "n0x")) { goto transition; }

        char *const placeholder = strstr(ptr, GRAPHVIZ_STYLE_PLACEHOLDER);
        if (NULL == placeholder) { goto transition; }

        memcpy(placeholder, GRAPHVIZ_HIDE, strlen(GRAPHVIZ_HIDE));

    transition:
        *end = backup_char;
        ptr = end + strlen(GRAPHVIZ_END_CLUSTER);
    }

    ptrx[length - 1] = clast, IO_CALL(munmap, ptrx, length);
    IO_CALL(fflush, graphviz_footer_fp);
}

static uint16_t
graphviz_hide_counter(void) {
    static uint16_t counter = 0;

    if (UINT16_MAX == counter) { panic("Graphviz hide counter overflow!"); }
    return counter++;
}

// Replace the node with an invisible one in the Graphviz clusters.
static void
clear_graphviz_cluster_node(const struct node node) {
    const size_t saddress_length = strlen("n0x000000000000");
    char saddress[32] = {0}, hide_saddress[32] = {0};

    XASSERT(sizeof(saddress) - 1 >= saddress_length);
    XASSERT(sizeof(hide_saddress) - 1 >= saddress_length);

    sprintf(saddress, "n%p", (void *)node.ports);

    char *ptr = NULL, *ptrx = NULL;
    size_t length = 0;
    char clast = '\0';
    ptr = ptrx = mmap_graphviz_footer(&length, &clast);
    if (NULL == ptr) { return; }

    ptr = strstr(ptr, saddress);
    if (NULL == ptr) {
        // The node is not in the Graphviz clusters.
        goto exit;
    }

    sprintf(
        hide_saddress,
        "hide%0*" PRIu16,
        (int)(saddress_length - strlen("hide")),
        graphviz_hide_counter());

    fprintf(
        graphviz_footer_fp,
        "\n" GRAPHVIZ_INDENT "%s [style=invis];\n",
        hide_saddress);

    do {
        memcpy(ptr, hide_saddress, saddress_length);
    } while ((ptr = strstr(ptr, saddress)));

exit:
    ptrx[length - 1] = clast, IO_CALL(munmap, ptrx, length);
    IO_CALL(fflush, graphviz_footer_fp);
}

#define DEFINED_clear_graphviz_cluster_node

#undef GRAPHVIZ_END_CLUSTER
#undef GRAPHVIZ_BEGIN_CLUSTER

#endif // OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS

inline static bool
graphviz_is_either_root(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    return SYMBOL_ROOT == f.ports[-1] || SYMBOL_ROOT == g.ports[-1];
}

inline static bool
graphviz_is_active_node(const struct node node) {
    XASSERT(node.ports);

    const struct node f = node, g = follow_port(&node.ports[0]);

    return is_interacting_with(f, g) && !graphviz_is_either_root(f, g);
}

inline static bool
graphviz_is_active_edge(const struct node node, const uint8_t i) {
    XASSERT(node.ports);

    const struct node f = node, g = follow_port(&node.ports[i]);

    return is_interaction(f, g) && !graphviz_is_either_root(f, g);
}

struct graphviz_context {
    FILE *stream;
    struct node_list *history;
    const bool is_reading_back;
};

COMPILER_NONNULL(1) //
static void
graphviz_draw_node(
    struct graphviz_context *const restrict ctx,
    const struct node node) {
    assert(ctx), XASSERT(ctx->stream);
    XASSERT(node.ports);

    const bool is_active = graphviz_is_active_node(node),
               is_root = SYMBOL_ROOT == node.ports[-1];

    fprintf(
        ctx->stream,
        // clang-format off
        GRAPHVIZ_INDENT "n%p"
        " [label=\"%s\""
        ", xlabel=<<FONT FACE=\"Courier\" COLOR=\"darkorange2\" POINT-SIZE=\"8\">%s</FONT>>"
        "%s%s%s];\n",
        // clang-format on
        (void *)node.ports,
        print_symbol(node.ports[-1]),
        graphviz_node_xlabel(node),
        (is_active ? ", color=" GRAPHVIZ_ACTIVE_COLOR : ""),
        (is_active ? ", penwidth=2.3" : ""),
        (is_root ? ", style=filled" : ""));
}

COMPILER_NONNULL(1) //
static void
graphviz_draw_edge(
    struct graphviz_context *const restrict ctx,
    const struct node source,
    const uint8_t i) {
    assert(ctx);
    XASSERT(source.ports);

    uint64_t *const target_port = DECODE_ADDRESS(source.ports[i]);
    const struct node target = node_of_port(target_port);

    const bool is_active = graphviz_is_active_edge(source, i);

    fprintf(
        ctx->stream,
        // clang-format off
        GRAPHVIZ_INDENT "n%p -> n%p [label=\" %s \", weight=%" PRIu8 ", tailport=%s"
        "%s%s%s%s];\n",
        // clang-format on
        (void *)source.ports,
        (void *)target.ports,
        graphviz_edge_label(source, i, ctx->is_reading_back),
        graphviz_edge_weight(source, i, ctx->is_reading_back),
        graphviz_edge_tailport(source, i, ctx->is_reading_back),
        (is_active ? ", color=" GRAPHVIZ_ACTIVE_COLOR : ""),
        (is_active ? ", penwidth=1.5" : ""),
        (IS_PRINCIPAL_PORT(*target_port) ? ", arrowhead=dot" : ""),
        (0 == i ? ", style=dashed" : ""));
}

COMPILER_NONNULL(1) //
static void
go_graphviz(
    struct graphviz_context *const restrict ctx,
    const struct node source,
    const uint8_t i) {
    assert(ctx), XASSERT(ctx->stream);
    XASSERT(source.ports);

    const struct node node = follow_port(&source.ports[i]);

    GUARD_NODE(ctx->history, node);

    graphviz_draw_node(ctx, node);

    FOR_ALL_PORTS (node, j, 0) { graphviz_draw_edge(ctx, node, j); }

    FOR_ALL_PORTS (node, j, 0) { go_graphviz(ctx, node, j); }
}

COMPILER_NONNULL(1, 2) //
static void
graphviz(
    const struct node_graph *const restrict graph,
    const char filename[const restrict]) {
    debug("%s(\"%s\")", __func__, filename);

    assert(graph);
    assert(filename);

#ifdef OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS
    if (NULL == graphviz_footer_fp) {
        // The file descriptor will be closed upon program termination.
        if (NULL == (graphviz_footer_fp = tmpfile())) {
            perror("tmpfile"), abort();
        }
    }
#endif

    FILE *fp = fopen(filename, "w");
    if (NULL == fp) { perror("fopen"), abort(); }

    fprintf(fp, "digraph {\n");
    fprintf(fp, GRAPHVIZ_INDENT "graph [nodesep=0.5, ranksep=0.8];\n");
    fprintf(fp, GRAPHVIZ_INDENT "node [fontname=\"bold helvetica\"];\n");
    fprintf(
        fp,
        GRAPHVIZ_INDENT
        "edge [fontname=\"bold helvetica\""
        ", fontsize=11"
        ", fontcolor=darkblue];\n");
    struct graphviz_context ctx = {
        .stream = fp,
        .history = NULL,
        .is_reading_back = graph->is_reading_back,
    };
    go_graphviz(&ctx, graph->root, 0);
    ctx.history = unvisit_all(ctx.history);
#ifdef OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS
    {
        postprocess_graphviz_footer();
        const long length = ftell(graphviz_footer_fp);
        rewind(graphviz_footer_fp);
        redirect_stream(graphviz_footer_fp, fp);
        fseek(graphviz_footer_fp, length, SEEK_SET);
    }
#endif
    fprintf(fp, "}\n");

    IO_CALL(fclose, fp);
}

#undef GRAPHVIZ_HIDE
#undef GRAPHVIZ_STYLE_PLACEHOLDER
#undef GRAPHVIZ_ACTIVE_COLOR
#undef GRAPHVIZ_ADDRESS_WIDTH_LINE
#undef GRAPHVIZ_INDENT_2X
#undef GRAPHVIZ_INDENT

#else

#define graphviz(graph, filename) ((void)0)

#endif // OPTISCOPE_ENABLE_GRAPHVIZ

#ifndef DEFINED_graphviz_commute_cluster
#define graphviz_commute_cluster(f_updates, g_updates, m, n) ((void)0)
#endif

#ifndef DEFINED_graphviz_beta_cluster
#define graphviz_beta_cluster(lhs, rhs) ((void)0)
#endif

#ifndef DEFINED_clear_graphviz_cluster_node
#define clear_graphviz_cluster_node(node) ((void)0)
#endif

#if !defined(NDEBUG) && defined(OPTISCOPE_ENABLE_STEP_BY_STEP)

COMPILER_NONNULL(1) //
static void
wait_for_user(const struct node_graph *const restrict graph) {
    assert(graph);

#ifdef OPTISCOPE_ENABLE_GRAPHVIZ
    graphviz(graph, "target/state.dot");
    if (system("./command/graphviz-state.sh") != 0) {
        panic("Failed to run `./command/graphviz-state.sh`!");
    }
#else
    (void)graph;
#endif

    printf("Press ENTER to proceed...");
    fflush(stdout);
    if (EOF == getchar()) { perror("getchar"), abort(); }
}

#else

#define wait_for_user(graph) ((void)0)

#endif // !defined(NDEBUG) && defined(OPTISCOPE_ENABLE_STEP_BY_STEP)

// Mark & sweep garbage collection
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_NONNULL(1) COMPILER_COLD //
static void
collect_garbage(
    const struct node_graph *const restrict graph,
    const struct node node) {
    assert(graph);
    XASSERT(node.ports);
    XASSERT(!graph->is_reading_back);

    struct multifocus *const stack = xcalloc(1, sizeof *stack);
    struct multifocus *const history = xcalloc(1, sizeof *history);

    focus_on(stack, node);

    const uint64_t altered_phase = graph->current_phase + 1;

    bool root_found = false;
    CONSUME_FOCUS (stack, f) {
        XASSERT(f.ports);

        if (SYMBOL_ROOT == f.ports[-1]) {
            root_found = true;
            break;
        }

        if (DECODE_PHASE_METADATA(f.ports[0]) == altered_phase) { continue; }
        f.ports[0] = SET_PHASE(f.ports[0], altered_phase);

        focus_on(history, f);

        switch (ports_count(f.ports[-1])) {
        case 3:
            focus_on(stack, follow_port(&f.ports[2])); //
            COMPILER_FALLTHROUGH;
        case 2:
            focus_on(stack, follow_port(&f.ports[1])); //
            COMPILER_FALLTHROUGH;
        case 1:
            focus_on(stack, follow_port(&f.ports[0])); //
            break;
        default: COMPILER_UNREACHABLE();
        }
    }

    if (root_found) {
        // Recover the current phase of the modified nodes.
        CONSUME_FOCUS (history, f) {
            f.ports[0] = SET_PHASE(f.ports[0], graph->current_phase);
        }
    } else {
        // Free the nodes not reachable from the root.
        CONSUME_FOCUS (history, f) {
            // Active nodes will be freed later before interacting.
            free_node_if_non_active(f);
        }
    }

    // Free all the allocated cells of the fallback list.
    CONSUME_LIST (iter, stack->fallback) {}

    free(stack);
    free(history);
}

// Interaction rules
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

// clang-format off
typedef void (*Rule)
    (struct node_graph *const restrict graph, struct node f, struct node g);
// clang-format on

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT //
inline static bool
is_annihilation(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    return is_interaction(f, g) && f.ports[-1] == g.ports[-1];
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT //
inline static bool
is_beta(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    return is_interaction(f, g) &&
           (SYMBOL_APPLICATOR == f.ports[-1] && SYMBOL_LAMBDA == g.ports[-1]);
}

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT //
inline static bool
is_commutation(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    return is_interaction(f, g) && !is_beta(f, g) && !is_beta(g, f) &&
           f.ports[-1] != g.ports[-1];
}

#ifdef OPTISCOPE_ENABLE_TRACING

COMPILER_NONNULL(1, 2) //
static void
debug_interaction(
    const char caller[const restrict],
    const struct node_graph *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(caller);
    assert(graph);

    char f_ssymbol[MAX_SSYMBOL_SIZE] = {0}, g_ssymbol[MAX_SSYMBOL_SIZE] = {0};
    strcpy(f_ssymbol, print_symbol(f.ports[-1])),
        strcpy(g_ssymbol, print_symbol(g.ports[-1]));
    debug(
        "%s(%p %s, %p %s)",
        caller,
        (void *)f.ports,
        f_ssymbol,
        (void *)g.ports,
        g_ssymbol);
    wait_for_user(graph);
}

#else

#define debug_interaction(caller, graph, f, g) ((void)0)

#endif // OPTISCOPE_ENABLE_TRACING

COMPILER_NONNULL(1) COMPILER_HOT //
static void
rewire_vertically(
    struct node_graph *const restrict graph,
    const struct node f,
    const struct node g,
    const uint8_t i) {
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);

    uint64_t *const lhs_target_port = DECODE_ADDRESS(f.ports[i]), //
        *const rhs_target_port = DECODE_ADDRESS(g.ports[i]);

    connect_ports(lhs_target_port, rhs_target_port);

    const struct node fx = node_of_port(lhs_target_port), //
        gx = node_of_port(rhs_target_port);

    register_pair_if_active(graph, fx, gx);
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
protrude_node(
    struct node_graph *const restrict graph,
    const struct node f,
    const uint64_t port) {
    assert(graph);
    XASSERT(f.ports);

    uint64_t *const target_port = DECODE_ADDRESS(port);

    connect_ports(&f.ports[0], target_port);

    if (IS_PRINCIPAL_PORT(*target_port)) {
        register_active_pair(graph, f, (struct node){target_port});
    }
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
annihilate(
    // clang-format off
    struct node_graph *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);
    assert(is_annihilation(f, g));

    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nannihilations++;
#endif

    // clang-format off
    const uint64_t n = ports_count(f.ports[-1]) - 1;
    switch (n) {
#define X(i) \
    case (i): rewire_vertically(graph, f, g, (i)); COMPILER_FALLTHROUGH
        X(2); X(1);
#undef X
    case 0: break;
    default: COMPILER_UNREACHABLE();
    }
    // clang-format on
}

COMPILER_UNUSED static const Rule annihilate_type_check = annihilate;

COMPILER_NONNULL(1) COMPILER_HOT //
static void
commute(struct node_graph *const restrict graph, struct node f, struct node g) {
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);
    assert(is_commutation(f, g));

prologue:;

    const bool with_lambda_or_delim =
        SYMBOL_LAMBDA == g.ports[-1] || IS_DELIMITER(g.ports[-1]);

    // Ensure that lambdas & delimiters are always `g`, to give `f` the
    // opportunitie to increment its index.
    if ((SYMBOL_LAMBDA == f.ports[-1] || IS_DELIMITER(f.ports[-1])) &&
        !with_lambda_or_delim) {
        const struct node h = f;
        f = g, g = h;
        goto prologue;
    }

    const int64_t i = symbol_index(f.ports[-1]), j = symbol_index(g.ports[-1]);

    // If both are delimiters, the one with a higher index should be `f`.
    if (IS_DELIMITER(f.ports[-1]) && IS_DELIMITER(g.ports[-1]) && j > i) {
        const struct node h = f;
        f = g, g = h;
        goto prologue;
    }

    // If `f` is a lambda & `g` is a delimiter, swap them so that the index of
    // `g` could be incremented.
    if (SYMBOL_LAMBDA == f.ports[-1] && IS_DELIMITER(g.ports[-1])) {
        const struct node h = f;
        f = g, g = h;
        goto prologue;
    }

    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->ncommutations++;
#endif

    const bool update_symbol = (SYMBOL_LAMBDA == g.ports[-1] && i >= 0) ||
                               (IS_DELIMITER(g.ports[-1]) && i >= j);

    const uint64_t f_symbol =
                       (update_symbol ? bump_index(f.ports[-1]) : f.ports[-1]),
                   g_symbol = g.ports[-1];

    const uint8_t n = ports_count(f.ports[-1]) - 1,
                  m = ports_count(g.ports[-1]) - 1;

    struct node f_updates[MAX_AUXILIARY_PORTS] = {{NULL}},
                g_updates[MAX_AUXILIARY_PORTS] = {{NULL}};

    // Connect the new nodes with the old ones, & register the new active nodes
    // for future interaction...

    switch (m) {
    case 2:
        f_updates[1] = alloc_node(graph, f_symbol);
        protrude_node(graph, f_updates[1], g.ports[1]);
        COMPILER_FALLTHROUGH;
    case 1:
        f_updates[0] = alloc_node(graph, f_symbol);
        protrude_node(graph, f_updates[0], g.ports[m]);
        break;
    case 0: break;
    default: COMPILER_UNREACHABLE();
    }

    switch (n) {
    case 2:
        g_updates[1] = alloc_node(graph, g_symbol);
        protrude_node(graph, g_updates[1], f.ports[2]);
        COMPILER_FALLTHROUGH;
    case 1:
        g_updates[0] = alloc_node(graph, g_symbol);
        protrude_node(graph, g_updates[0], f.ports[1]);
        break;
    case 0: break;
    default: COMPILER_UNREACHABLE();
    }

    XASSERT(m <= 2), XASSERT(n <= 2);

    // Connect the new nodes among themselves.
    // Manually unrolling this loop into a sequence of conditionnes did not give
    // us a noticeable performance benefit.
    for (uint8_t i = 0; i < m; i++) {
        for (uint8_t j = 0; j < n; j++) {
            connect_ports(
                &f_updates[i].ports[j + 1], &g_updates[j].ports[m - i]);
        }
    }

    graphviz_commute_cluster(f_updates, g_updates, m, n);
}

COMPILER_UNUSED static const Rule commute_type_check = commute;

COMPILER_NONNULL(1) COMPILER_HOT //
static void
beta(
    // clang-format off
    struct node_graph *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    assert(graph);
    XASSERT(!graph->is_reading_back);
    XASSERT(f.ports), XASSERT(g.ports);
    assert(is_interaction(f, g));
    XASSERT(SYMBOL_APPLICATOR == f.ports[-1]),
        XASSERT(SYMBOL_LAMBDA == g.ports[-1]);

    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nbetas++;
#endif

    const struct node lhs = alloc_node(graph, SYMBOL_DELIMITER(UINT64_C(0)));
    const struct node rhs = alloc_node(graph, SYMBOL_DELIMITER(UINT64_C(0)));

    // clang-format off
    uint64_t *const targets[] = {
        DECODE_ADDRESS(f.ports[1]), DECODE_ADDRESS(g.ports[2]),
        DECODE_ADDRESS(f.ports[2]), DECODE_ADDRESS(g.ports[1]),
    };
    // clang-format on

    connect_ports(&lhs.ports[0], targets[0]);
    connect_ports(&rhs.ports[0], targets[2]);

    connect_ports(&lhs.ports[1], targets[1]);
    connect_ports(&rhs.ports[1], targets[3]);

    register_node_if_active(graph, lhs);
    register_node_if_active(graph, rhs);

    const struct node binder = follow_port(&g.ports[1]);
    if (SYMBOL_ERASER == binder.ports[-1]) {
        // There is a chance that the argument is fully disconnected from the
        // root; if so, we must garbage-collect it.
        collect_garbage(graph, binder);
    }

    if (!is_garbage_node(&binder.ports[0])) {
        graphviz_beta_cluster(&lhs.ports[0], &rhs.ports[0]);
    }
}

COMPILER_UNUSED static const Rule beta_type_check = beta;

// See `u64_value_of_function`.
COMPILER_CONST COMPILER_HOT //
inline static uint64_t (*function_of_u64_value(const uint64_t function))(
    uint64_t value) {
    XASSERT(0 != function);

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
    return (uint64_t (*)(uint64_t value))(void *)function;
#pragma GCC diagnostic pop
}

COMPILER_HOT //
inline static uint64_t
invoke_function(const uint64_t function, const uint64_t value) {
    XASSERT(0 != function);

    return (function_of_u64_value(function))(value);
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
invoke_rule(
    // clang-format off
    struct node_graph *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    assert(graph);
    XASSERT(!graph->is_reading_back);
    XASSERT(f.ports), XASSERT(g.ports);
    assert(is_interaction(f, g));
    XASSERT(SYMBOL_INVOKE == f.ports[-1]), XASSERT(SYMBOL_CELL == g.ports[-1]);

    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->ninvocations++;
#endif

    const struct node cell = alloc_node(graph, SYMBOL_CELL);
    connect_ports(&cell.ports[0], DECODE_ADDRESS(f.ports[1]));
    cell.ports[1] = invoke_function(f.ports[2], g.ports[1]);
}

COMPILER_UNUSED static const Rule invoke_type_check = invoke_rule;

COMPILER_NONNULL(1, 2) COMPILER_HOT //
static void
interact(
    struct node_graph *const restrict graph,
    const Rule rule,
    const struct node f) {
    assert(graph);
    assert(rule);
    XASSERT(f.ports);

    const struct node g = follow_port(&f.ports[0]);
    XASSERT(g.ports);

    if (DECODE_PHASE_METADATA(f.ports[0]) == graph->current_phase + 1) {
        // This active node was previously marked as garbage.
        goto cleanup;
    }

    rule(graph, f, g);

cleanup:
    free_node(f), free_node(g);
}

// The read-back phases
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#define PHASE_INITIAL      UINT64_C(0)
#define PHASE_UNWIND       UINT64_C(1)
#define PHASE_SCOPE_REMOVE UINT64_C(2)
#define PHASE_LOOP_CUT     UINT64_C(3)

COMPILER_NONNULL(1) COMPILER_HOT //
static struct node_list *
iterate_nodes(const struct node_graph *graph, const struct symbol_range range) {
    assert(graph);
    XASSERT(graph->root.ports);

    struct multifocus *stack = xcalloc(1, sizeof *stack);
    struct node_list *collection = NULL;

    focus_on(stack, graph->root);

    CONSUME_FOCUS (stack, node) {
        XASSERT(node.ports);

        if (DECODE_PHASE_METADATA(node.ports[0]) == graph->current_phase) {
            continue;
        }
        node.ports[0] = SET_PHASE(node.ports[0], graph->current_phase);

        if (symbol_is_in_range(range, node.ports[-1])) {
            collection = visit(collection, node);
        }

        switch (ports_count(node.ports[-1])) {
        case 3:
            focus_on(stack, follow_port(&node.ports[2]));
            COMPILER_FALLTHROUGH;
        case 2:
            focus_on(stack, follow_port(&node.ports[1]));
            COMPILER_FALLTHROUGH;
        case 1:
            focus_on(stack, follow_port(&node.ports[0])); //
            break;
        default: COMPILER_UNREACHABLE();
        }
    }

    free(stack);

    return collection;
}

#define PROCESS_NODE_IN_PHASE(graph, node)                                     \
    do {                                                                       \
        debug("%s(%s)", __func__, print_node(node));                           \
        wait_for_user(graph);                                                  \
    } while (false)

COMPILER_NONNULL(1) //
static void
unwind(struct node_graph *const restrict graph) {
    assert(graph);
    assert(is_normalized_graph(graph));

    graph->current_phase = PHASE_UNWIND;

    CONSUME_LIST (
        iter, iterate_nodes(graph, SYMBOL_RANGE_1(SYMBOL_APPLICATOR))) {
        const struct node f = iter->node;
        XASSERT(f.ports);
        PROCESS_NODE_IN_PHASE(graph, f);

        // clang-format off
        CONNECT_NODE(f,
            DECODE_ADDRESS(f.ports[1]), DECODE_ADDRESS(f.ports[2]),
            DECODE_ADDRESS(f.ports[0]));
        // clang-format on

        register_node_if_active(graph, f);
    }
}

COMPILER_NONNULL(1) //
static void
register_active_scopes(
    struct node_graph *const restrict graph,
    struct node_list *new_scopes) {
    assert(graph);

    CONSUME_LIST (iter, new_scopes) {
        const struct node f = iter->node, g = follow_port(&iter->node.ports[0]);

        // Protect from focusing on both active scopes.
        // See <https://github.com/etiams/optiscope/issues/2>.
        if (!(SYMBOL_S == g.ports[-1] && compare_node_ptrs(f, g) > 0)) {
            register_node_if_active(graph, f);
        }
    }
}

COMPILER_NONNULL(1) //
static void
scope_remove(struct node_graph *const restrict graph) {
    assert(graph);
    assert(is_normalized_graph(graph));

    graph->current_phase = PHASE_SCOPE_REMOVE;

    struct node_list *new_scopes = NULL;
    CONSUME_LIST (iter, iterate_nodes(graph, DELIMITER_RANGE)) {
        const struct node node = iter->node;
        XASSERT(node.ports);
        PROCESS_NODE_IN_PHASE(graph, node);

        const struct node scope = alloc_node(graph, SYMBOL_S);
        // clang-format off
        CONNECT_NODE(scope,
            DECODE_ADDRESS(node.ports[1]), DECODE_ADDRESS(node.ports[0]));
        // clang-format on

        new_scopes = visit(new_scopes, scope);
        free_node(node);
    }

    register_active_scopes(graph, new_scopes);
}

COMPILER_NONNULL(1) //
static void
loop_cut(struct node_graph *const restrict graph) {
    assert(graph);
    assert(is_normalized_graph(graph));

    graph->current_phase = PHASE_LOOP_CUT;

    CONSUME_LIST (iter, iterate_nodes(graph, SYMBOL_RANGE_1(SYMBOL_LAMBDA))) {
        const struct node node = iter->node;
        XASSERT(node.ports);
        PROCESS_NODE_IN_PHASE(graph, node);

        struct node side_eraser = alloc_node(graph, SYMBOL_ERASER);
        struct node bottom_eraser = alloc_node(graph, SYMBOL_ERASER);
        uint64_t *const binder_port = DECODE_ADDRESS(node.ports[1]);

        connect_ports(&node.ports[1], &side_eraser.ports[0]);
        connect_ports(&bottom_eraser.ports[0], binder_port);

        register_node_if_active(graph, bottom_eraser);
    }
}

#undef PROCESS_NODE_IN_PHASE

// Conversion to a lambda term string
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_NONNULL(1) //
static void
to_lambda_string(
    FILE *const restrict stream,
    const uint64_t i,
    const struct node node) {
    assert(stream);
    XASSERT(node.ports);

    switch (node.ports[-1]) {
    case SYMBOL_APPLICATOR:
        fprintf(stream, "(");
        to_lambda_string(stream, i, follow_port(&node.ports[2]));
        fprintf(stream, " ");
        to_lambda_string(stream, i, follow_port(&node.ports[1]));
        fprintf(stream, ")");
        return;
    case SYMBOL_LAMBDA:
        fprintf(stream, "(λ ");
        to_lambda_string(stream, i, follow_port(&node.ports[2]));
        fprintf(stream, ")");
        return;
    case SYMBOL_ERASER: fprintf(stream, "%" PRIu64, i); return;
    case SYMBOL_S:
        to_lambda_string(stream, i + 1, follow_port(&node.ports[1]));
        return;
    case SYMBOL_CELL:
        fprintf(stream, "cell[%" PRIu64 "]", node.ports[1]);
        return;
    case SYMBOL_INVOKE:
        fprintf(stream, "(invoke[%#llx] ", (unsigned long long)node.ports[1]);
        to_lambda_string(stream, i, follow_port(&node.ports[0]));
        fprintf(stream, ")");
        return;
    default: break;
    }

    if (!IS_DUPLICATOR(node.ports[-1])) {
        // Other symbols must be already removed at this point.
        COMPILER_UNREACHABLE();
    }

    for (uint8_t k = 1, l = 2; k <= 2; k++, l--) {
        const struct node neighbour = follow_port(&node.ports[k]);
        if (SYMBOL_ERASER == neighbour.ports[-1]) {
            const struct node body = follow_port(&node.ports[l]);
            to_lambda_string(stream, i, body);
            return;
        }
    }

    COMPILER_UNREACHABLE();
}

// The lambda term interface
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

enum lambda_term_type {
    LAMBDA_TERM_APPLICATOR,
    LAMBDA_TERM_LAMBDA,
    LAMBDA_TERM_VAR,
    LAMBDA_TERM_CELL,
    LAMBDA_TERM_INVOKE,
};

struct applicator_payload {
    struct lambda_term *rator;
    struct lambda_term *rand;
};

struct lambda_payload {
    struct lambda_term *body;
    uint64_t **dup_ports; // the pointer to the next duplicator tree
                          // port; dynamically assigned
    uint64_t lvl;         // the de Bruijn level; dynamically assigned
};

struct invoke_payload {
    uint64_t (*function)(uint64_t value);
    struct lambda_term *rand;
};

union lambda_term_payload {
    struct applicator_payload applicator;
    struct lambda_payload lambda;
    struct lambda_payload *var; // the pointer to the binding lambda
    uint64_t cell;
    struct invoke_payload invoke;
};

struct lambda_term {
    enum lambda_term_type ty;
    union lambda_term_payload payload;
};

extern LambdaTerm
applicator(const restrict LambdaTerm rator, const restrict LambdaTerm rand) {
    assert(rator), assert(rand);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_APPLICATOR;
    term->payload.applicator.rator = rator;
    term->payload.applicator.rand = rand;

    return term;
}

extern LambdaTerm
prelambda(void) {
    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_LAMBDA;
    term->payload.lambda.body = NULL;
    term->payload.lambda.dup_ports = NULL;
    term->payload.lambda.lvl = 0;

    return term;
}

extern LambdaTerm
link_lambda_body(
    const restrict LambdaTerm binder,
    const restrict LambdaTerm body) {
    assert(binder), assert(body);

    binder->payload.lambda.body = body;

    return binder;
}

extern LambdaTerm
var(const restrict LambdaTerm binder) {
    assert(binder);
    XASSERT(LAMBDA_TERM_LAMBDA == binder->ty);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_VAR;
    term->payload.var = &binder->payload.lambda;

    return term;
}

extern LambdaTerm
cell(const uint64_t value) {
    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_CELL;
    term->payload.cell = value;

    return term;
}

extern LambdaTerm
invoke(
    uint64_t (*const function)(uint64_t value),
    const restrict LambdaTerm rand) {
    assert(function), assert(rand);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_INVOKE;
    term->payload.invoke.function = function;
    term->payload.invoke.rand = rand;

    return term;
}

// Conversion from a lambda term
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1, 2) //
static uint64_t
count_binder_usage(
    const struct lambda_term *const restrict term,
    const struct lambda_payload *const restrict lambda) {
    assert(term);
    assert(lambda);

    switch (term->ty) {
    case LAMBDA_TERM_APPLICATOR: {
        struct lambda_term *const rator = term->payload.applicator.rator, //
            *const rand = term->payload.applicator.rand;
        XASSERT(rator);
        XASSERT(rand);

        return count_binder_usage(rator, lambda) +
               count_binder_usage(rand, lambda);
    }
    case LAMBDA_TERM_LAMBDA: {
        struct lambda_term *const body = term->payload.lambda.body;
        XASSERT(body);

        return count_binder_usage(body, lambda);
    }
    case LAMBDA_TERM_VAR: {
        struct lambda_payload *this_lambda = term->payload.var;
        XASSERT(this_lambda);

        return lambda == this_lambda;
    }
    case LAMBDA_TERM_CELL: return 0;
    case LAMBDA_TERM_INVOKE: {
        struct lambda_term *const rand = term->payload.invoke.rand;
        XASSERT(rand);

        return count_binder_usage(rand, lambda);
    }
    default: COMPILER_UNREACHABLE();
    }
}

COMPILER_RETURNS_NONNULL COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1, 2) //
static uint64_t *
build_delimiter_sequence(
    struct node_graph *const restrict graph,
    uint64_t *const restrict binder_port,
    const uint64_t n) {
    assert(graph);
    assert(binder_port);
    XASSERT(n > 0);

    struct node current = alloc_node(graph, SYMBOL_DELIMITER(UINT64_C(0)));
    uint64_t *const result = &current.ports[1];
    for (uint64_t i = 1; i < n; i++) {
        const struct node delim =
            alloc_node(graph, SYMBOL_DELIMITER(UINT64_C(0)));
        connect_ports(&current.ports[0], &delim.ports[1]);
        current = delim;
    }

    connect_ports(&current.ports[0], binder_port);

    return result;
}

COMPILER_RETURNS_NONNULL COMPILER_NONNULL(1, 2) COMPILER_WARN_UNUSED_RESULT //
static uint64_t **
build_duplicator_tree(
    struct node_graph *const restrict graph,
    uint64_t *const restrict binder_port,
    const uint64_t n) {
    assert(graph);
    assert(binder_port);
    XASSERT(n >= 1);

    uint64_t **const ports = xmalloc(sizeof ports[0] * n);

    struct node current = alloc_node(graph, SYMBOL_DUPLICATOR(UINT64_C(0)));
    struct node eraser = alloc_node(graph, SYMBOL_ERASER);

    ports[0] = &current.ports[1];
    connect_ports(&current.ports[2], &eraser.ports[0]);

    for (uint64_t i = 1; i < n; i++) {
        const struct node dup =
            alloc_node(graph, SYMBOL_DUPLICATOR(UINT64_C(0)));
        ports[i] = &dup.ports[1];
        connect_ports(&dup.ports[2], &current.ports[0]);
        current = dup;
    }

    connect_ports(&current.ports[0], binder_port);

    return ports;
}

COMPILER_CONST COMPILER_WARN_UNUSED_RESULT //
inline static uint64_t
de_bruijn_level_to_index(const uint64_t lvl, const uint64_t var) {
    return lvl - var - 1;
}

// Casting a function pointer to `void *` is not safe by the standard, but many
// implementationnes permit it because of dynamic loading (e.g., `dlopen`).
// Here, we perform a two-step conversion: we first cast the user-provided
// pointer to `void *` & then to `uint64_t`.
COMPILER_CONST COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1) //
inline static uint64_t
u64_value_of_function(uint64_t (*const function)(uint64_t value)) {
    assert(function);

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
    return (uint64_t)(void *)function;
#pragma GCC diagnostic pop
}

COMPILER_NONNULL(1, 2, 3) //
static void
go_of_lambda_term(
    struct node_graph *const restrict graph,
    struct lambda_term *const restrict term,
    uint64_t *const restrict output_port,
    const uint64_t lvl) {
    assert(graph);
    assert(term);
    assert(output_port);

    switch (term->ty) {
    case LAMBDA_TERM_APPLICATOR: {
        struct lambda_term *const rator = term->payload.applicator.rator, //
            *const rand = term->payload.applicator.rand;
        XASSERT(rator);
        XASSERT(rand);

        const struct node applicator = alloc_node(graph, SYMBOL_APPLICATOR);
        go_of_lambda_term(graph, rator, &applicator.ports[0], lvl);
        go_of_lambda_term(graph, rand, &applicator.ports[2], lvl);
        connect_ports(&applicator.ports[1], output_port);

        const struct node lambda = follow_port(&applicator.ports[0]);
        if (is_beta(applicator, lambda)) {
            focus_on(graph->betas, applicator); //
        }

        break;
    }
    case LAMBDA_TERM_LAMBDA: {
        struct lambda_payload *const tlambda = &term->payload.lambda;
        struct lambda_term *const body = term->payload.lambda.body;
        XASSERT(tlambda);
        XASSERT(body);

        const struct node lambda = alloc_node(graph, SYMBOL_LAMBDA);
        const uint64_t nvars = count_binder_usage(body, tlambda);
        uint64_t **dup_ports = NULL;
        if (0 == nvars) {
            const struct node eraser = alloc_node(graph, SYMBOL_ERASER);
            connect_ports(&lambda.ports[1], &eraser.ports[0]);
        } else {
            dup_ports = build_duplicator_tree(
                graph, &lambda.ports[1], nvars /* nvars >= 1 */);
        }
        tlambda->dup_ports = dup_ports;
        tlambda->lvl = lvl;
        go_of_lambda_term(graph, body, &lambda.ports[2], lvl + 1);
        connect_ports(&lambda.ports[0], output_port);
        if (dup_ports) { free(dup_ports); }

        break;
    }
    case LAMBDA_TERM_VAR: {
        struct lambda_payload *const lambda = term->payload.var;
        XASSERT(lambda);

        const uint64_t idx = de_bruijn_level_to_index(lvl, lambda->lvl);
        if (0 == idx) {
            connect_ports(lambda->dup_ports[0], output_port);
        } else {
            uint64_t *const delimiter_port =
                build_delimiter_sequence(graph, lambda->dup_ports[0], idx);
            connect_ports(delimiter_port, output_port);
        }
        lambda->dup_ports++;

        break;
    }
    case LAMBDA_TERM_CELL: {
        const uint64_t value = term->payload.cell;

        const struct node cell = alloc_node(graph, SYMBOL_CELL);
        cell.ports[1] = value;
        connect_ports(&cell.ports[0], output_port);

        break;
    }
    case LAMBDA_TERM_INVOKE: {
        uint64_t (*const function)(uint64_t value) =
            term->payload.invoke.function;
        struct lambda_term *const rand = term->payload.invoke.rand;
        XASSERT(function);
        XASSERT(rand);

        const struct node invocation = alloc_node(graph, SYMBOL_INVOKE);
        invocation.ports[2] = u64_value_of_function(function);
        go_of_lambda_term(graph, rand, &invocation.ports[0], lvl);
        connect_ports(&invocation.ports[1], output_port);
        register_node_if_active(
            graph, invocation); // either commutation or invocation

        break;
    }
    default: COMPILER_UNREACHABLE();
    }

    // This function takes ownership of the whole `term` object.
    free(term);
}

COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1) //
static struct node_graph
of_lambda_term(struct lambda_term *const restrict term) {
    assert(term);

    const struct node root = xmalloc_node(SYMBOL_ROOT, PHASE_INITIAL);
    const struct node eraser = xmalloc_node(SYMBOL_ERASER, PHASE_INITIAL);

    // Since the principle root port is connected to the eraser, the root will
    // never interact with "real" nodes.
    connect_ports(&root.ports[0], &eraser.ports[0]);

    struct node_graph graph = {
        .root = root,
        .annihilations = xcalloc(1, sizeof *graph.annihilations),
        .commutations = xcalloc(1, sizeof *graph.commutations),
        .betas = xcalloc(1, sizeof *graph.betas),
        .invocations = xcalloc(1, sizeof *graph.invocations),
        .current_phase = PHASE_INITIAL,
        .is_reading_back = false,

#ifdef OPTISCOPE_ENABLE_STATS
        .nannihilations = 0,
        .ncommutations = 0,
        .nbetas = 0,
        .ninvocations = 0,
#endif
    };

    go_of_lambda_term(&graph, term, &root.ports[1], 0);

    return graph;
}

// The complete algorithm
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_NONNULL(1) //
static void
normalize_x_rules(struct node_graph *const restrict graph) {
    debug("%s()", __func__);

    assert(graph);

    do {
        if (graph->is_reading_back) { goto auxiliary_rules; }

        CONSUME_FOCUS (graph->betas, f) { interact(graph, beta, f); }
        CONSUME_FOCUS (graph->invocations, f) {
            interact(graph, invoke_rule, f);
        }

    auxiliary_rules:
        CONSUME_FOCUS (graph->annihilations, f) {
            interact(graph, annihilate, f);
        }
        CONSUME_FOCUS (graph->commutations, f) { //
            interact(graph, commute, f);
        }
    } while (!is_normalized_graph(graph));
}

extern void
optiscope_algorithm(
    FILE *const restrict stream,            // if `NULL`, do not read back
    struct lambda_term *const restrict term // must not be `NULL`
) {
    debug("%s()", __func__);

    assert(term);

    struct node_graph graph = of_lambda_term(term);

    // Initiall normalization.
    {
        graphviz(&graph, "target/0-initial.dot");
        normalize_x_rules(&graph);
        graphviz(&graph, "target/0-initialx.dot");
    }

#ifdef OPTISCOPE_ENABLE_STATS
    printf("Annihilation interactions: %" PRIu64 "\n", graph.nannihilations);
    printf("Commutation interactions: %" PRIu64 "\n", graph.ncommutations);
    printf("Beta interactions: %" PRIu64 "\n", graph.nbetas);
    printf("Native function calls: %" PRIu64 "\n", graph.ninvocations);
    printf(
        "Total interactions: %" PRIu64 "\n",
        graph.nannihilations + graph.ncommutations + graph.nbetas +
            graph.ninvocations);
#endif

    if (NULL == stream) { goto cleanup; }

    ITERATE_ONCE (
        finish, graph.is_reading_back = true, graph.is_reading_back = false) {
        // Phase #1 {
        unwind(&graph);
        graphviz(&graph, "target/1-unwound.dot");
        normalize_x_rules(&graph);
        graphviz(&graph, "target/1-unwoundx.dot");
        // }

        // Phase #2 {
        scope_remove(&graph);
        graphviz(&graph, "target/2-unscoped.dot");
        normalize_x_rules(&graph);
        graphviz(&graph, "target/2-unscopedx.dot");
        // }

        // Phase #3 {
        loop_cut(&graph);
        graphviz(&graph, "target/3-unlooped.dot");
        normalize_x_rules(&graph);
        graphviz(&graph, "target/3-unloopedx.dot");
        // }
    }

    to_lambda_string(stream, 0, follow_port(&graph.root.ports[1]));

cleanup:
    assert(is_normalized_graph(&graph));
    free_graph(&graph);
}
