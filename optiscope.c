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

// Header inclusions
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#include "optiscope.h"

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

// Debug assertions
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

// Assertions that are checked at program run-time.
#if defined(__GNUC__) && defined(NDEBUG)
#define XASSERT(condition) (!(condition) ? __builtin_unreachable() : (void)0)
#else
#define XASSERT assert
#endif

// Assertions that are checked at compile-time.
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
#define PHASE_METADATA_BITS  UINT64_C(4)
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
     (EFFECTIVE_ADDRESS_BITS + OFFSET_METADATA_BITS))

#define ENCODE_ADDRESS(metadata, address)                                      \
    (((address) & ADDRESS_MASK) | (metadata))
#define SIGN_EXTEND(n)                                                         \
    ((uint64_t)((int64_t)((n) << UNUSED_ADDRESS_BITS) >> UNUSED_ADDRESS_BITS))
#define DECODE_ADDRESS(address)                                                \
    ((uint64_t *)(SIGN_EXTEND((address) & ADDRESS_MASK)))
#define DECODE_ADDRESS_METADATA(address) (((address) & ~ADDRESS_MASK))

#define PORT_VALUE(offset, phase, address)                                     \
    ENCODE_ADDRESS(ENCODE_METADATA((offset), (phase)), (address))

#define IS_PRINCIPAL_PORT(port) (0 == DECODE_OFFSET_METADATA(port))

STATIC_ASSERT(CHAR_BIT == 8, "The byte width must be 8 bits!");
STATIC_ASSERT(
    sizeof(uint64_t *) == sizeof(uint64_t),
    "The machine word width must be 64 bits!");
STATIC_ASSERT(
    sizeof(uint64_t (*)(uint64_t value)) <= sizeof(uint64_t),
    "Function handles must fit in `uint64_t`!");

#define MIN_REGULAR_SYMBOL   UINT64_C(0)
#define MAX_REGULAR_SYMBOL   UINT64_C(11)
#define INDEX_RANGE          UINT64_C(9223372036854775802)
#define MAX_DUPLICATOR_INDEX (MAX_REGULAR_SYMBOL + INDEX_RANGE)
#define MAX_DELIMITER_INDEX  (MAX_DUPLICATOR_INDEX + INDEX_RANGE)
#define MAX_PORTS            UINT64_C(4)
#define MAX_AUXILIARY_PORTS  (MAX_PORTS - 1)

STATIC_ASSERT(
    UINT64_MAX == UINT64_C(18446744073709551615),
    "`uint64_t` must have the expected range of [0; 2^64 - 1]!");
STATIC_ASSERT(
    UINT64_MAX == MAX_DELIMITER_INDEX,
    "Every bit of a symbol must be used!");

#define SYMBOL_ROOT            UINT64_C(0)
#define SYMBOL_GARBAGE         UINT64_C(1)
#define SYMBOL_APPLICATOR      UINT64_C(2)
#define SYMBOL_LAMBDA          UINT64_C(3)
#define SYMBOL_ERASER          UINT64_C(4)
#define SYMBOL_S               UINT64_C(5)
#define SYMBOL_CELL            UINT64_C(6)
#define SYMBOL_UNARY_CALL      UINT64_C(7)
#define SYMBOL_BINARY_CALL     UINT64_C(8)
#define SYMBOL_BINARY_CALL_AUX UINT64_C(9)
#define SYMBOL_IF_THEN_ELSE    UINT64_C(10)
#define SYMBOL_FIX             UINT64_C(11)
#define SYMBOL_DUPLICATOR(i)   (MAX_REGULAR_SYMBOL + 1 + (i))
#define SYMBOL_DELIMITER(i)    (MAX_DUPLICATOR_INDEX + 1 + (i))

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
#define SYMBOL_FULL_RANGE SYMBOL_RANGE(SYMBOL_ROOT + 1, UINT64_MAX)
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
    case SYMBOL_ROOT:
    case SYMBOL_S:
    case SYMBOL_UNARY_CALL:
    case SYMBOL_BINARY_CALL_AUX:
    case SYMBOL_FIX: return 2;
    case SYMBOL_APPLICATOR:
    case SYMBOL_LAMBDA:
    case SYMBOL_BINARY_CALL: return 3;
    case SYMBOL_ERASER:
    case SYMBOL_CELL: return 1;
    case SYMBOL_IF_THEN_ELSE: return 4;
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
COMPILER_NONNULL(1) COMPILER_HOT //
inline static uint64_t *
get_principal_port(uint64_t *const restrict port) {
    assert(port);

    return (port - DECODE_OFFSET_METADATA(port[0]));
}

COMPILER_NONNULL(1, 2) COMPILER_HOT //
inline static void
connect_port_to(
    uint64_t *const restrict port,
    const uint64_t *const restrict another) {
    assert(port);
    assert(another);
    XASSERT(port != another);
    assert(DECODE_ADDRESS(*port) != another);

    const uint64_t port_metadata = DECODE_ADDRESS_METADATA(*port);

    *port = ENCODE_ADDRESS(port_metadata, (uint64_t)another);

    assert(DECODE_ADDRESS(*port) == another);
    assert(DECODE_ADDRESS_METADATA(*port) == port_metadata);
}

COMPILER_NONNULL(1, 2) COMPILER_HOT COMPILER_FLATTEN //
inline static void
connect_ports(uint64_t *const restrict lhs, uint64_t *const restrict rhs) {
    debug("%p 🔗 %p", (void *)lhs, (void *)rhs);

    // Delegate the assertions to `connect_ports_to`.
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
    case SYMBOL_UNARY_CALL:
    case SYMBOL_BINARY_CALL:
    case SYMBOL_BINARY_CALL_AUX:
    case SYMBOL_IF_THEN_ELSE:
    case SYMBOL_FIX: return -1;
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
    case SYMBOL_UNARY_CALL: sprintf(buffer, "unary-call"); break;
    case SYMBOL_BINARY_CALL: sprintf(buffer, "binary-call"); break;
    case SYMBOL_BINARY_CALL_AUX: sprintf(buffer, "binary-call-aux"); break;
    case SYMBOL_IF_THEN_ELSE: sprintf(buffer, "if-then-else"); break;
    case SYMBOL_FIX: sprintf(buffer, "fix"); break;
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

COMPILER_WARN_UNUSED_RESULT COMPILER_HOT //
inline static uint64_t
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

#define PHASE_WEAK_REDUCTION UINT64_C(0)
#define PHASE_FULL_REDUCTION UINT64_C(1)
#define PHASE_UNWIND         UINT64_C(2)
#define PHASE_SCOPE_REMOVE   UINT64_C(3)
#define PHASE_LOOP_CUT       UINT64_C(4)
#define PHASE_GARBAGE        UINT64_C(5)

COMPILER_NONNULL(1) COMPILER_HOT //
inline static void
set_phase(uint64_t *const restrict port, const uint64_t phase) {
    assert(port);
    assert(IS_PRINCIPAL_PORT(*port));

    const uint64_t mask =
        UINT64_C(0xC3FFFFFFFFFFFFFF); /* clear the phase bits (61-58) */

    *port = (*port & mask) | (phase << EFFECTIVE_ADDRESS_BITS);

    assert(DECODE_PHASE_METADATA(*port) == phase);
}

// Native function pointers
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

// Casting a function pointer to `void *` is not safe by the standard, but many
// implementations permit it because of dynamic loading (e.g., `dlopen`).
// Here, we performe a two-step conversion: we first cast the user-provided
// pointer to `void *` & then to `uint64_t`.
#define U64_OF_FUNCTION(function) ((uint64_t)(void *)(function))

#define UNARY_FUNCTION_OF_U64(function)                                        \
    ((uint64_t (*)(uint64_t))(void *)(function))
#define BINARY_FUNCTION_OF_U64(function)                                       \
    ((uint64_t (*)(uint64_t, uint64_t))(void *)(function))

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

// Dynamically adjusted chunk list sizes are not an option: they did actually
// degrade the performance.
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
POOL_ALLOCATOR(unary_call, sizeof(uint64_t) * 4)
POOL_ALLOCATOR(binary_call, sizeof(uint64_t) * 5)
POOL_ALLOCATOR(binary_call_aux, sizeof(uint64_t) * 5)
POOL_ALLOCATOR(if_then_else, sizeof(uint64_t) * 5)
POOL_ALLOCATOR(fix, sizeof(uint64_t) * 3)

#define ALLOC_POOL_OBJECT(pool_name)        pool_name##_alloc(pool_name)
#define FREE_POOL_OBJECT(pool_name, object) pool_name##_free(pool_name, object)

#define POOLS                                                                  \
    X(applicator_pool)                                                         \
    X(lambda_pool)                                                             \
    X(eraser_pool)                                                             \
    X(scope_pool)                                                              \
    X(duplicator_pool)                                                         \
    X(delimiter_pool)                                                          \
    X(cell_pool)                                                               \
    X(unary_call_pool)                                                         \
    X(binary_call_pool)                                                        \
    X(binary_call_aux_pool)                                                    \
    X(if_then_else_pool)                                                       \
    X(fix_pool)

#define X(pool_name) static struct pool_name *pool_name = NULL;
POOLS
#undef X

#define X(pool_name)                                                           \
    {                                                                          \
        XASSERT(NULL == pool_name);                                            \
        pool_name = pool_name##_create();                                      \
        XASSERT(pool_name);                                                    \
    }

// clang-format off
extern void optiscope_open_pools(void) { POOLS }
// clang-format on

#undef X

#define X(pool_name)                                                           \
    {                                                                          \
        XASSERT(pool_name);                                                    \
        pool_name##_close(pool_name);                                          \
        pool_name = NULL;                                                      \
    }

// clang-format off
extern void optiscope_close_pools(void) { POOLS }
// clang-format on

#undef X

#undef POOLS

#undef POOL_ALLOCATOR
#undef POOL_CHUNK_LIST_SIZE

// Nodes functionalitie
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

struct node {
    uint64_t *ports;
};

STATIC_ASSERT(
    sizeof(struct node) == sizeof(uint64_t *),
    "`struct node` must be as tiny as a pointer!");

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
static struct node
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
        // clang-format off
        sprintf(
            buffer, "%s [%p, %p, %p]", ssymbol,
            (void *)&p[0], (void *)&p[1], (void *)&p[2]
        );
        // clang-format on
        break;
    case 4:
        // clang-format off
        sprintf(
            buffer, "%s [%p, %p, %p, %p]", ssymbol,
            (void *)&p[0], (void *)&p[1], (void *)&p[2], (void *)&p[3]
        );
        // clang-format on
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
free_node_if_not_active(const struct node f) {
    XASSERT(f.ports);

    if (is_garbage_node(f.ports)) { return; }

    uint64_t *const target_port = DECODE_ADDRESS(f.ports[0]);
    if (is_garbage_node(target_port)) { return; }

    const struct node g = node_of_port(target_port);

    if (is_interacting_with(f, g)) { return; }

    free_node(f);
}

// Linked lists functionalitie
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

// Multifocuses functionalitie
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

#ifndef OPTISCOPE_MULTIFOCUS_COUNT
#define OPTISCOPE_MULTIFOCUS_COUNT                                             \
    ((1024 * 1024) / sizeof(struct node)) // 1 MB default
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

COMPILER_NONNULL(1) //
static void
reset_multifocus(struct multifocus *const restrict focus) {
    assert(focus);

    focus->count = 0;
    CLEAR_MEMORY(focus->initial);
    focus->fallback = NULL;
}

#define CONSUME_MULTIFOCUS(focus, f)                                           \
    for (struct node f = {NULL};                                               \
         (focus)->count > 0 ? (f = unfocus(focus), true) : false;              \
         (void)0)

// The main context functionalitie
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

// clang-format off
#define CONTEXT_MULTIFOCUSES \
    X(betas) X(annihilations) X(commutations) \
    X(unary_calls) X(binary_calls) X(binary_calls_aux) \
    X(if_then_elses) X(fixpoints)
// clang-format on

struct context {
    struct node root;
    uint64_t phase;

#define X(focus_name) struct multifocus *focus_name;
    CONTEXT_MULTIFOCUSES
#undef X

#ifdef OPTISCOPE_ENABLE_STATS
#define X(focus_name) uint64_t n##focus_name;
    CONTEXT_MULTIFOCUSES
#undef X
#endif

    struct multifocus *gc_focus, *gc_history;
};

COMPILER_NONNULL(1) COMPILER_COLD //
static void
free_context(struct context *const restrict graph);

// clang-format off
COMPILER_MALLOC(free_context, 1) COMPILER_RETURNS_NONNULL
COMPILER_WARN_UNUSED_RESULT COMPILER_COLD
// clang-format on
static struct context *alloc_context(void) {
    const struct node root = //
        xmalloc_node(SYMBOL_ROOT, PHASE_WEAK_REDUCTION);
    const struct node eraser =
        xmalloc_node(SYMBOL_ERASER, PHASE_WEAK_REDUCTION);

    // Since the principle root port is connected to the eraser, the root will
    // never interact with "real" nodes.
    connect_ports(&root.ports[0], &eraser.ports[0]);

    struct context *const graph = xmalloc(sizeof *graph);
    graph->root = root;
    graph->phase = PHASE_WEAK_REDUCTION;

#define X(focus_name) graph->focus_name = NULL;
    CONTEXT_MULTIFOCUSES
#undef X

#ifdef OPTISCOPE_ENABLE_STATS
#define X(focus_name) graph->n##focus_name = 0;
    CONTEXT_MULTIFOCUSES
#undef X
#endif

    graph->gc_focus = xcalloc(1, sizeof *graph->gc_focus);
    graph->gc_history = xcalloc(1, sizeof *graph->gc_history);

    return graph;
}

COMPILER_NONNULL(1) COMPILER_COLD //
static void
free_context(struct context *const restrict graph) {
    debug("%s()", __func__);

    assert(graph);
    XASSERT(graph->root.ports);

    free(DECODE_ADDRESS(graph->root.ports[0]) - 1 /* back to the symbol */);
    free(graph->root.ports - 1 /* back to the symbol */);

    // clang-format off
#define X(focus_name) \
    { \
        XASSERT(graph->focus_name); \
        XASSERT(0 == graph->focus_name->count); \
        free(graph->focus_name); \
    }
    // clang-format on

    CONTEXT_MULTIFOCUSES
    X(gc_focus)
    X(gc_history)

#undef X

    free(graph);
}

COMPILER_PURE COMPILER_NONNULL(1) COMPILER_HOT //
inline static bool
is_normalized_graph(const struct context *const restrict graph) {
    assert(graph);

#define X(focus_name) (0 == graph->focus_name->count) &&
    return CONTEXT_MULTIFOCUSES true;
#undef X
}

#ifdef OPTISCOPE_ENABLE_STATS

COMPILER_NONNULL(1) //
static void
print_stats(const struct context *const restrict graph) {
    assert(graph);

    const uint64_t ncalls =
        graph->nunary_calls + graph->nbinary_calls + graph->nbinary_calls_aux;

    printf("Annihilation interactions: %" PRIu64 "\n", graph->nannihilations);
    printf("Commutation interactions: %" PRIu64 "\n", graph->ncommutations);
    printf("Beta interactions: %" PRIu64 "\n", graph->nbetas);
    printf("Native function calls: %" PRIu64 "\n", ncalls);
    printf("If-then-elses: %" PRIu64 "\n", graph->nif_then_elses);
    printf("Fixpoints: %" PRIu64 "\n", graph->nfixpoints);

    printf(
        "Total interactions: %" PRIu64 "\n",
        graph->nannihilations + graph->ncommutations + graph->nbetas + //
            ncalls + graph->nif_then_elses + graph->nfixpoints);
}

#else

#define print_stats(graph) ((void)0)

#endif // OPTISCOPE_ENABLE_STATS

COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1) COMPILER_HOT //
static struct node
alloc_node_from(
    struct context *const restrict graph,
    const uint64_t symbol,
    const struct node *const restrict prototype) {
    assert(graph);
    XASSERT(SYMBOL_ROOT != symbol);
    if (prototype) { XASSERT(prototype->ports); }

#ifndef NDEBUG
    if (prototype) {
        if (IS_DUPLICATOR(symbol)) {
            assert(IS_DUPLICATOR(prototype->ports[-1]));
        } else if (IS_DELIMITER(symbol)) {
            assert(IS_DELIMITER(prototype->ports[-1]));
        } else {
            assert(symbol == prototype->ports[-1]);
        }
    }
#endif

    // While it might seem that preallocation caches can increase performance,
    // in fact, they introduced almost a 2x slowdown.
    (void)0;

    uint64_t *ports = NULL;

    switch (symbol) {
        // clang-format off
    case SYMBOL_APPLICATOR:
        ports = ALLOC_POOL_OBJECT(applicator_pool); goto set_ports_2;
    case SYMBOL_LAMBDA:
        ports = ALLOC_POOL_OBJECT(lambda_pool); goto set_ports_2;
    case SYMBOL_ERASER:
        ports = ALLOC_POOL_OBJECT(eraser_pool); goto set_ports_0;
    case SYMBOL_S:
        ports = ALLOC_POOL_OBJECT(scope_pool); goto set_ports_1;
        // clang-format on
    case SYMBOL_CELL:
        ports = ALLOC_POOL_OBJECT(cell_pool);
        if (prototype) { ports[1] = prototype->ports[1]; }
        goto set_ports_0;
    case SYMBOL_UNARY_CALL:
        ports = ALLOC_POOL_OBJECT(unary_call_pool);
        if (prototype) { ports[2] = prototype->ports[2]; }
        goto set_ports_1;
    case SYMBOL_BINARY_CALL:
        ports = ALLOC_POOL_OBJECT(binary_call_pool);
        if (prototype) { ports[3] = prototype->ports[3]; }
        goto set_ports_2;
    case SYMBOL_BINARY_CALL_AUX:
        ports = ALLOC_POOL_OBJECT(binary_call_aux_pool);
        if (prototype) {
            ports[2] = prototype->ports[2], ports[3] = prototype->ports[3];
        }
        goto set_ports_1;
    case SYMBOL_IF_THEN_ELSE:
        ports = ALLOC_POOL_OBJECT(if_then_else_pool);
        goto set_ports_3;
    case SYMBOL_FIX:
        ports = ALLOC_POOL_OBJECT(fix_pool);
        goto set_ports_1;
        // clang-format off
    duplicator:
        ports = ALLOC_POOL_OBJECT(duplicator_pool); goto set_ports_2;
    delimiter:
        ports = ALLOC_POOL_OBJECT(delimiter_pool); goto set_ports_1;
        // clang-format on
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    }

    COMPILER_UNREACHABLE();

set_ports_3:
    ports[3] = PORT_VALUE(UINT64_C(3), UINT64_C(0), UINT64_C(0));
set_ports_2:
    ports[2] = PORT_VALUE(UINT64_C(2), UINT64_C(0), UINT64_C(0));
set_ports_1:
    ports[1] = PORT_VALUE(UINT64_C(1), UINT64_C(0), UINT64_C(0));
set_ports_0:
    ports[0] = PORT_VALUE(UINT64_C(0), graph->phase, UINT64_C(0));

    ports[-1] = symbol;

    debug("🔨 %s", print_node((struct node){ports}));

    return (struct node){ports};
}

#define alloc_node(graph, symbol) alloc_node_from((graph), (symbol), NULL)

// clang-format off
#ifdef OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS
static void clear_graphviz_cluster_node(const struct node node);
#endif
// clang-format on

COMPILER_HOT //
static void
free_node(const struct node node) {
    debug("🧹 %p", (void *)node.ports);

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
    case SYMBOL_APPLICATOR: FREE_POOL_OBJECT(applicator_pool, p); break;
    case SYMBOL_LAMBDA: FREE_POOL_OBJECT(lambda_pool, p); break;
    case SYMBOL_ERASER: FREE_POOL_OBJECT(eraser_pool, p); break;
    case SYMBOL_S: FREE_POOL_OBJECT(scope_pool, p); break;
    case SYMBOL_CELL: FREE_POOL_OBJECT(cell_pool, p); break;
    case SYMBOL_UNARY_CALL: FREE_POOL_OBJECT(unary_call_pool, p); break;
    case SYMBOL_BINARY_CALL: FREE_POOL_OBJECT(binary_call_pool, p); break;
    case SYMBOL_BINARY_CALL_AUX:
        FREE_POOL_OBJECT(binary_call_aux_pool, p);
        break;
    case SYMBOL_IF_THEN_ELSE: FREE_POOL_OBJECT(if_then_else_pool, p); break;
    case SYMBOL_FIX: FREE_POOL_OBJECT(fix_pool, p); break;
    default:
        if (symbol <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (symbol <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        FREE_POOL_OBJECT(duplicator_pool, p);
        break;
    delimiter:
        FREE_POOL_OBJECT(delimiter_pool, p);
        break;
    }
}

#define DISPATCH_ACTIVE_PAIR(f, g)                                             \
    do {                                                                       \
        const uint64_t fsym = f.ports[-1], gsym = g.ports[-1];                 \
                                                                               \
        switch (fsym) {                                                        \
        case SYMBOL_APPLICATOR:                                                \
            if (SYMBOL_LAMBDA == gsym) BETA(f, g);                             \
            else COMMUTE(f, g);                                                \
            break;                                                             \
        case SYMBOL_LAMBDA:                                                    \
            if (SYMBOL_APPLICATOR == gsym) BETA(g, f);                         \
            else if (SYMBOL_FIX == gsym) FIX(g, f);                            \
            else COMMUTE(f, g);                                                \
            break;                                                             \
        case SYMBOL_CELL:                                                      \
            switch (gsym) {                                                    \
            case SYMBOL_UNARY_CALL: UNARY_CALL(g, f); break;                   \
            case SYMBOL_BINARY_CALL: BINARY_CALL(g, f); break;                 \
            case SYMBOL_BINARY_CALL_AUX: BINARY_CALL_AUX(g, f); break;         \
            case SYMBOL_IF_THEN_ELSE: IF_THEN_ELSE(g, f); break;               \
            default: COMMUTE(f, g);                                            \
            }                                                                  \
            break;                                                             \
        case SYMBOL_UNARY_CALL:                                                \
            if (SYMBOL_CELL == gsym) UNARY_CALL(f, g);                         \
            else COMMUTE(f, g);                                                \
            break;                                                             \
        case SYMBOL_BINARY_CALL:                                               \
            if (SYMBOL_CELL == gsym) BINARY_CALL(f, g);                        \
            else COMMUTE(f, g);                                                \
            break;                                                             \
        case SYMBOL_BINARY_CALL_AUX:                                           \
            if (SYMBOL_CELL == gsym) BINARY_CALL_AUX(f, g);                    \
            else COMMUTE(f, g);                                                \
            break;                                                             \
        case SYMBOL_IF_THEN_ELSE:                                              \
            if (SYMBOL_CELL == gsym) IF_THEN_ELSE(f, g);                       \
            else COMMUTE(f, g);                                                \
            break;                                                             \
        case SYMBOL_FIX:                                                       \
            if (SYMBOL_LAMBDA == gsym) FIX(f, g);                              \
            else COMMUTE(f, g);                                                \
            break;                                                             \
        default:                                                               \
            if (fsym == gsym) ANNIHILATE(f, g);                                \
            else COMMUTE(f, g);                                                \
        }                                                                      \
    } while (false)

COMPILER_NONNULL(1) COMPILER_HOT //
static void
register_active_pair(
    struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);
    assert(is_interaction(f, g));

    if (PHASE_WEAK_REDUCTION == graph->phase) { return; }

#define BETA(f, g)            focus_on(graph->betas, f)
#define UNARY_CALL(f, g)      focus_on(graph->unary_calls, f)
#define BINARY_CALL(f, g)     focus_on(graph->binary_calls, f)
#define BINARY_CALL_AUX(f, g) focus_on(graph->binary_calls_aux, f)
#define IF_THEN_ELSE(f, g)    focus_on(graph->if_then_elses, f)
#define FIX(f, g)             focus_on(graph->fixpoints, f)
#define ANNIHILATE(f, g)      focus_on(graph->annihilations, f)
#define COMMUTE(f, g)         focus_on(graph->commutations, f)

    DISPATCH_ACTIVE_PAIR(f, g);

#undef COMMUTE
#undef ANNIHILATE
#undef FIX
#undef IF_THEN_ELSE
#undef BINARY_CALL_AUX
#undef BINARY_CALL
#undef UNARY_CALL
#undef BETA
}

COMPILER_NONNULL(1) COMPILER_HOT //
inline static void
register_pair_if_active(
    struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);

    if (PHASE_WEAK_REDUCTION == graph->phase) { return; }

    if (is_interaction(f, g)) { register_active_pair(graph, f, g); }
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
register_node_if_active(
    struct context *const restrict graph,
    const struct node node) {
    assert(graph);
    XASSERT(node.ports);

    if (PHASE_WEAK_REDUCTION == graph->phase) { return; }

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
    case 4:
        sprintf(
            buffer,
            GRAPHVIZ_ADDRESS_WIDTH_LINE
            "<BR/>| %p |<BR/>| %p |<BR/>| %p |<BR/>| %p |<BR/>" //
            GRAPHVIZ_ADDRESS_WIDTH_LINE,
            (void *)&p[0],
            (void *)&p[1],
            (void *)&p[2],
            (void *)&p[3]);
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

    switch (node.ports[-1]) {
    case SYMBOL_ROOT:
    case SYMBOL_S:
        switch (i) {
        case 0: return "n";
        case 1: return "s";
        default: COMPILER_UNREACHABLE();
        }
    case SYMBOL_APPLICATOR:
        if ((is_reading_back ? 0 : 1) == i) return "n";
        else if ((is_reading_back ? 2 : 0) == i) return "s";
        else if ((is_reading_back ? 1 : 2) == i) return "e";
        else COMPILER_UNREACHABLE();
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
    case SYMBOL_BINARY_CALL:
        switch (i) {
        case 0: return "sw";
        case 1: return "n";
        case 2: return "se";
        default: COMPILER_UNREACHABLE();
        }
    case SYMBOL_IF_THEN_ELSE:
        switch (i) {
        case 0: return "sw";
        case 1: return "n";
        case 2: return "se";
        case 3: return "s";
        default: COMPILER_UNREACHABLE();
        }
    default:
        if (node.ports[-1] <= MAX_DUPLICATOR_INDEX) goto duplicator;
        else if (node.ports[-1] <= MAX_DELIMITER_INDEX) goto delimiter;
        else COMPILER_UNREACHABLE();
    duplicator:
        switch (i) {
        case 0: return "s";
        case 1: return "nw";
        case 2: return "ne";
        default: COMPILER_UNREACHABLE();
        }
    delimiter:
    case SYMBOL_UNARY_CALL:
    case SYMBOL_BINARY_CALL_AUX:
    case SYMBOL_FIX:
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

    // Initialize the (invisible) connections between the nodes.
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
        "%s" // node connections
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
    const struct context *const restrict graph,
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
        .is_reading_back = graph->phase >= PHASE_UNWIND,
    };
    go_graphviz(&ctx, graph->root, 0);
    ctx.history = unvisit_all(ctx.history);
#ifdef OPTISCOPE_ENABLE_GRAPHVIZ_CLUSTERS
    {
        postprocess_graphviz_footer();
        const long length = ftell(graphviz_footer_fp);
        rewind(graphviz_footer_fp);
        optiscope_redirect_stream(graphviz_footer_fp, fp);
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
wait_for_user(const struct context *const restrict graph) {
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

COMPILER_NONNULL(1, 3) //
static void
mark(
    const struct context *const restrict graph,
    const struct node node,
    bool *const restrict root_found) {
    assert(graph);
    XASSERT(graph->phase < PHASE_UNWIND);
    XASSERT(node.ports);
    XASSERT(SYMBOL_ROOT != node.ports);
    assert(root_found);

    focus_on(graph->gc_focus, node);

    CONSUME_MULTIFOCUS (graph->gc_focus, f) {
        XASSERT(f.ports);

        if (DECODE_PHASE_METADATA(f.ports[0]) == PHASE_GARBAGE) { //
            continue;
        }
        set_phase(&f.ports[0], PHASE_GARBAGE);
        focus_on(graph->gc_history, f);

        // clang-format off
        if (SYMBOL_ROOT == f.ports[-1]) { *root_found = true; break; }
        // clang-format on

        const uint8_t nports = ports_count(f.ports[-1]);
        XASSERT(nports <= MAX_PORTS);

        for (uint8_t i = 0; i < nports; i++) {
            focus_on(graph->gc_focus, follow_port(&f.ports[i]));
        }
    }

    // Free all the allocated cells of the fallback list.
    CONSUME_LIST (iter, graph->gc_focus->fallback) {}

    // This focus is to be reused in the next garbage collection.
    reset_multifocus(graph->gc_focus);
}

COMPILER_NONNULL(1) //
static void
sweep(const struct context *const restrict graph, const bool root_found) {
    assert(graph);
    XASSERT(graph->phase < PHASE_UNWIND);

    if (root_found) {
        CONSUME_MULTIFOCUS (graph->gc_history, f) {
            set_phase(&f.ports[0], graph->phase);
        }
    } else {
        CONSUME_MULTIFOCUS (graph->gc_history, f) {
            if (graph->phase >= PHASE_FULL_REDUCTION) {
                // Delay freeing this node until it is popped from a
                // corresponding multifocus.
                free_node_if_not_active(f);
            } else {
                free_node(f);
            }
        }
    }
}

COMPILER_NONNULL(1) //
static void
collect_garbage(
    const struct context *const restrict graph,
    const struct node node) {
    assert(graph);
    XASSERT(graph->phase < PHASE_UNWIND);
    XASSERT(node.ports);
    XASSERT(graph->gc_focus), XASSERT(0 == graph->gc_focus->count);
    XASSERT(graph->gc_history), XASSERT(0 == graph->gc_history->count);

    bool root_found = false;
    mark(graph, node, &root_found);
    sweep(graph, root_found);
}

// Interaction rules
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT //
inline static bool
is_beta(const struct node f, const struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);

    return SYMBOL_APPLICATOR == f.ports[-1] && SYMBOL_LAMBDA == g.ports[-1];
}

#ifndef NDEBUG

static void
assert_annihilation(const struct node f, const struct node g) {
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(SYMBOL_APPLICATOR != f.ports[-1]);
    assert(SYMBOL_LAMBDA != f.ports[-1]);
    assert(f.ports[-1] == g.ports[-1]);
}

static void
assert_beta(
    const struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    assert(graph->phase < PHASE_UNWIND);
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(is_beta(f, g));
}

static void
assert_commutation(const struct node f, const struct node g) {
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(!is_beta(f, g)), assert(!is_beta(g, f));
    assert(f.ports[-1] != g.ports[-1]);
}

static void
assert_unary_call(
    const struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    assert(graph->phase < PHASE_UNWIND);
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(SYMBOL_UNARY_CALL == f.ports[-1]);
    assert(SYMBOL_CELL == g.ports[-1]);
}

static void
assert_binary_call(
    const struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    assert(graph->phase < PHASE_UNWIND);
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(SYMBOL_BINARY_CALL == f.ports[-1]);
    assert(SYMBOL_CELL == g.ports[-1]);
}

static void
assert_binary_call_aux(
    const struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    assert(graph->phase < PHASE_UNWIND);
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(SYMBOL_BINARY_CALL_AUX == f.ports[-1]);
    assert(SYMBOL_CELL == g.ports[-1]);
}

static void
assert_if_then_else(
    const struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    assert(graph->phase < PHASE_UNWIND);
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(SYMBOL_IF_THEN_ELSE == f.ports[-1]);
    assert(SYMBOL_CELL == g.ports[-1]);
}

static void
assert_fix(
    const struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    assert(graph->phase < PHASE_UNWIND);
    assert(f.ports), assert(g.ports);
    assert(is_interaction(f, g));
    assert(SYMBOL_FIX == f.ports[-1]);
    assert(SYMBOL_LAMBDA == g.ports[-1]);
}

#else

#define assert_annihilation(f, g)           ((void)0)
#define assert_beta(graph, f, g)            ((void)0)
#define assert_commutation(f, g)            ((void)0)
#define assert_unary_call(graph, f, g)      ((void)0)
#define assert_binary_call(graph, f, g)     ((void)0)
#define assert_binary_call_aux(graph, f, g) ((void)0)
#define assert_if_then_else(graph, f, g)    ((void)0)
#define assert_fix(graph, f, g)             ((void)0)

#endif // NDEBUG

#ifdef OPTISCOPE_ENABLE_TRACING

COMPILER_NONNULL(1, 2) //
static void
debug_interaction(
    const char caller[const restrict],
    const struct context *const restrict graph,
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
inline static void
rewire_vertically(
    struct context *const restrict graph,
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

COMPILER_NONNULL(1, 3) COMPILER_HOT //
inline static void
protrude_node(
    struct context *const restrict graph,
    const struct node f,
    uint64_t *const restrict port) {
    assert(graph);
    XASSERT(f.ports);
    assert(port);

    connect_ports(&f.ports[0], port);

    if (IS_PRINCIPAL_PORT(*port)) {
        register_active_pair(graph, f, (struct node){port});
    }
}

// clang-format off
typedef void (*Rule)
    (struct context *const restrict graph, struct node f, struct node g);
// clang-format on

#define TYPE_CHECK_RULE(name)                                                  \
    COMPILER_UNUSED static const Rule name##_type_check = name

COMPILER_NONNULL(1) COMPILER_HOT //
static void
annihilate(
    // clang-format off
    struct context *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    XASSERT(f.ports), XASSERT(g.ports);
    assert_annihilation(f, g);
    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nannihilations++;
#endif

    const uint64_t n = ports_count(f.ports[-1]) - 1;
    XASSERT(n <= MAX_AUXILIARY_PORTS);

    for (uint8_t i = 1; i <= n; i++) {
        // Respective ports must have the same semantic meaning.
        rewire_vertically(graph, f, g, i);
    }
}

TYPE_CHECK_RULE(annihilate);

COMPILER_NONNULL(1) COMPILER_HOT //
static void
commute(struct context *const restrict graph, struct node f, struct node g) {
    XASSERT(f.ports), XASSERT(g.ports);
    assert_commutation(f, g);

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

    const uint64_t fsym =
                       (update_symbol ? bump_index(f.ports[-1]) : f.ports[-1]),
                   gsym = g.ports[-1];

    const uint8_t n = ports_count(f.ports[-1]) - 1,
                  m = ports_count(g.ports[-1]) - 1;

    struct node f_updates[MAX_AUXILIARY_PORTS] = {{NULL}},
                g_updates[MAX_AUXILIARY_PORTS] = {{NULL}};

    // Hint the compiler to automatically unroll the following loops.
    XASSERT(m <= MAX_AUXILIARY_PORTS), XASSERT(n <= MAX_AUXILIARY_PORTS);

    for (uint8_t i = 0; i < m; i++) {
        f_updates[i] = alloc_node_from(graph, fsym, &f);
        // clang-format off
        protrude_node(graph,
            f_updates[i], DECODE_ADDRESS(g.ports[m - i]));
        // clang-format on
    }
    for (uint8_t i = 0; i < n; i++) {
        g_updates[i] = alloc_node_from(graph, gsym, &g);
        // clang-format off
        protrude_node(graph,
            g_updates[i], DECODE_ADDRESS(f.ports[i + 1]));
        // clang-format on
    }

    for (uint8_t i = 0; i < m; i++) {
        for (uint8_t j = 0; j < n; j++) {
            connect_ports(
                &f_updates[i].ports[j + 1], &g_updates[j].ports[m - i]);
        }
    }

    graphviz_commute_cluster(f_updates, g_updates, m, n);
}

TYPE_CHECK_RULE(commute);

COMPILER_NONNULL(1) COMPILER_HOT //
static void
beta(
    // clang-format off
    struct context *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    XASSERT(f.ports), XASSERT(g.ports);
    assert_beta(graph, f, g);
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

TYPE_CHECK_RULE(beta);

COMPILER_NONNULL(1) COMPILER_HOT //
static void
do_unary_call(
    // clang-format off
    struct context *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    XASSERT(f.ports), XASSERT(g.ports);
    assert_unary_call(graph, f, g);
    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nunary_calls++;
#endif

    const struct node cell = alloc_node(graph, SYMBOL_CELL);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
    cell.ports[1] = (UNARY_FUNCTION_OF_U64(f.ports[2]))(g.ports[1]);
#pragma GCC diagnostic pop
    protrude_node(graph, cell, DECODE_ADDRESS(f.ports[1]));
}

TYPE_CHECK_RULE(do_unary_call);

COMPILER_NONNULL(1) COMPILER_HOT //
static void
do_binary_call(
    // clang-format off
    struct context *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    XASSERT(f.ports), XASSERT(g.ports);
    assert_binary_call(graph, f, g);
    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nbinary_calls++;
#endif

    const struct node aux = alloc_node(graph, SYMBOL_BINARY_CALL_AUX);
    connect_ports(&aux.ports[1], DECODE_ADDRESS(f.ports[1]));
    aux.ports[2] = f.ports[3];
    aux.ports[3] = g.ports[1];
    protrude_node(graph, aux, DECODE_ADDRESS(f.ports[2]));
}

TYPE_CHECK_RULE(do_binary_call);

COMPILER_NONNULL(1) COMPILER_HOT //
static void
do_binary_call_aux(
    // clang-format off
    struct context *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    XASSERT(f.ports), XASSERT(g.ports);
    assert_binary_call_aux(graph, f, g);
    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nbinary_calls_aux++;
#endif

    const struct node cell = alloc_node(graph, SYMBOL_CELL);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
    cell.ports[1] =
        (BINARY_FUNCTION_OF_U64(f.ports[2]))(f.ports[3], g.ports[1]);
#pragma GCC diagnostic pop
    protrude_node(graph, cell, DECODE_ADDRESS(f.ports[1]));
}

TYPE_CHECK_RULE(do_binary_call_aux);

COMPILER_NONNULL(1, 3, 4) COMPILER_HOT //
static void
connect_branch(
    struct context *const restrict graph,
    const struct node f,
    uint64_t *const restrict choice,
    uint64_t *const restrict other) {
    assert(graph);
    XASSERT(f.ports);
    assert(choice);
    assert(other);

    const struct node eraser = alloc_node(graph, SYMBOL_ERASER);

    connect_ports(DECODE_ADDRESS(f.ports[1]), choice);
    register_node_if_active(graph, node_of_port(choice));

    connect_ports(&eraser.ports[0], other);

    collect_garbage(graph, eraser);
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
do_if_then_else(
    // clang-format off
    struct context *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    XASSERT(f.ports), XASSERT(g.ports);
    assert_if_then_else(graph, f, g);
    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nif_then_elses++;
#endif

    uint64_t *const if_then = DECODE_ADDRESS(f.ports[3]), //
        *const if_else = DECODE_ADDRESS(f.ports[2]);

    if (g.ports[1]) {
        connect_branch(graph, f, if_then, if_else);
    } else {
        connect_branch(graph, f, if_else, if_then);
    }
}

TYPE_CHECK_RULE(do_if_then_else);

COMPILER_NONNULL(1) COMPILER_HOT //
static void
do_fix(
    // clang-format off
    struct context *const restrict graph, const struct node f, const struct node g) {
    // clang-format on
    XASSERT(f.ports), XASSERT(g.ports);
    assert_fix(graph, f, g);
    debug_interaction(__func__, graph, f, g);

#ifdef OPTISCOPE_ENABLE_STATS
    graph->nfixpoints++;
#endif

    const struct node lhs_delim =
        alloc_node(graph, SYMBOL_DELIMITER(UINT64_C(0)));
    const struct node rhs_delim =
        alloc_node(graph, SYMBOL_DELIMITER(UINT64_C(0)));

    const struct node body_dup = alloc_node(graph, SYMBOL_DUPLICATOR(0));
    const struct node binder_dup = alloc_node(graph, SYMBOL_DUPLICATOR(0));

    const struct node fix = alloc_node(graph, SYMBOL_FIX);
    const struct node lambda = alloc_node(graph, SYMBOL_LAMBDA);

    connect_ports(&lhs_delim.ports[1], &body_dup.ports[1]);
    connect_ports(&rhs_delim.ports[1], &binder_dup.ports[1]);
    connect_ports(&fix.ports[0], &lambda.ports[0]);
    connect_ports(&fix.ports[1], &rhs_delim.ports[0]);
    connect_ports(&lambda.ports[1], &binder_dup.ports[2]);
    connect_ports(&lambda.ports[2], &body_dup.ports[2]);

    connect_ports(&lhs_delim.ports[0], DECODE_ADDRESS(f.ports[1]));
    connect_ports(&body_dup.ports[0], DECODE_ADDRESS(g.ports[2]));
    connect_ports(&binder_dup.ports[0], DECODE_ADDRESS(g.ports[1]));

    register_active_pair(graph, fix, lambda);
    register_node_if_active(graph, lhs_delim);
}

TYPE_CHECK_RULE(do_fix);

#undef TYPE_CHECK_RULE

COMPILER_NONNULL(1, 2) COMPILER_HOT //
static void
interact(
    struct context *const restrict graph,
    const Rule rule,
    const struct node f) {
    assert(graph);
    assert(rule);
    XASSERT(f.ports);

    // TODO: this check is not needed, because garbage nodes should not occur in
    // multifocuses in the first place.
    if (is_garbage_node(&f.ports[0])) { return; }

    const struct node g = follow_port(&f.ports[0]);
    XASSERT(g.ports);

    if (DECODE_PHASE_METADATA(f.ports[0]) == PHASE_GARBAGE) {
        // This active node was previously marked as garbage.
        goto cleanup;
    }

    // TODO: this check should not be needed as well!
    if (!is_interaction(f, g)) { return; }

    rule(graph, f, g);

cleanup:
    free_node(f), free_node(g);
}

// The read-back phases
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_NONNULL(1) COMPILER_HOT //
static struct node_list *
iterate_nodes(
    const struct context *const graph,
    const struct symbol_range range) {
    assert(graph);
    XASSERT(graph->root.ports);

    struct multifocus *focus = xcalloc(1, sizeof *focus);
    struct node_list *collection = NULL;

    focus_on(focus, graph->root);

    CONSUME_MULTIFOCUS (focus, node) {
        XASSERT(node.ports);

        if (DECODE_PHASE_METADATA(node.ports[0]) == graph->phase) { continue; }
        set_phase(&node.ports[0], graph->phase);

        if (symbol_is_in_range(range, node.ports[-1])) {
            collection = visit(collection, node);
        }

        const uint8_t nports = ports_count(node.ports[-1]);
        XASSERT(nports <= MAX_PORTS);

        // For some reason, the order of iteration matters here...
        for (int8_t i = nports - 1; i >= 0; i--) {
            focus_on(focus, follow_port(&node.ports[i]));
        }
    }

    free(focus);

    return collection;
}

#define PROCESS_NODE_IN_PHASE(graph, node)                                     \
    do {                                                                       \
        debug("%s(%s)", __func__, print_node(node));                           \
        wait_for_user(graph);                                                  \
    } while (false)

COMPILER_NONNULL(1) //
static void
unwind(struct context *const restrict graph) {
    assert(graph);
    assert(is_normalized_graph(graph));

    graph->phase = PHASE_UNWIND;

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
    struct context *const restrict graph,
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
scope_remove(struct context *const restrict graph) {
    assert(graph);
    assert(is_normalized_graph(graph));

    graph->phase = PHASE_SCOPE_REMOVE;

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
loop_cut(struct context *const restrict graph) {
    assert(graph);
    assert(is_normalized_graph(graph));

    graph->phase = PHASE_LOOP_CUT;

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
    default: break;
    }

    if (!IS_DUPLICATOR(node.ports[-1])) {
        // Other symbols must be already removed at this point.
        panic("Unexpected node symbol!: %s", print_symbol(node.ports[-1]));
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
    LAMBDA_TERM_UNARY_CALL,
    LAMBDA_TERM_BINARY_CALL,
    LAMBDA_TERM_IF_THEN_ELSE,
    LAMBDA_TERM_FIX,
};

struct applicator_data {
    struct lambda_term *rator, *rand;
};

struct lambda_data {
    struct lambda_term *body;
    uint64_t **dup_ports; // the pointer to the next duplicator tree
                          // port; dynamically assigned
    uint64_t lvl;         // the de Bruijn level; dynamically assigned
};

struct unary_call_data {
    uint64_t (*function)(uint64_t);
    struct lambda_term *rand;
};

struct binary_call_data {
    uint64_t (*function)(uint64_t, uint64_t);
    struct lambda_term *lhs, *rhs;
};

struct if_then_else_data {
    struct lambda_term *condition;
    struct lambda_term *if_then, *if_else;
};

struct fix_data {
    struct lambda_term *f;
};

union lambda_term_data {
    struct applicator_data applicator;
    struct lambda_data lambda;
    struct lambda_data *var; // the pointer to the binding lambda
    uint64_t cell;
    struct unary_call_data u_call;
    struct binary_call_data b_call;
    struct if_then_else_data ite;
    struct fix_data fix;
};

struct lambda_term {
    enum lambda_term_type ty;
    union lambda_term_data data;
};

extern LambdaTerm
applicator(const restrict LambdaTerm rator, const restrict LambdaTerm rand) {
    assert(rator), assert(rand);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_APPLICATOR;
    term->data.applicator.rator = rator;
    term->data.applicator.rand = rand;

    return term;
}

extern LambdaTerm
prelambda(void) {
    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_LAMBDA;
    term->data.lambda.body = NULL;
    term->data.lambda.dup_ports = NULL;
    term->data.lambda.lvl = 0;

    return term;
}

extern LambdaTerm
link_lambda_body(
    const restrict LambdaTerm binder,
    const restrict LambdaTerm body) {
    assert(binder), assert(body);

    binder->data.lambda.body = body;

    return binder;
}

extern LambdaTerm
var(const restrict LambdaTerm binder) {
    assert(binder);
    assert(LAMBDA_TERM_LAMBDA == binder->ty);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_VAR;
    term->data.var = &binder->data.lambda;

    return term;
}

extern LambdaTerm
cell(const uint64_t value) {
    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_CELL;
    term->data.cell = value;

    return term;
}

extern LambdaTerm
unary_call(
    uint64_t (*const function)(uint64_t),
    const restrict LambdaTerm rand) {
    assert(function);
    assert(rand);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_UNARY_CALL;
    term->data.u_call.function = function;
    term->data.u_call.rand = rand;

    return term;
}

extern LambdaTerm
binary_call(
    uint64_t (*const function)(uint64_t, uint64_t),
    const restrict LambdaTerm lhs,
    const restrict LambdaTerm rhs) {
    assert(function);
    assert(lhs), assert(rhs);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_BINARY_CALL;
    term->data.b_call.function = function;
    term->data.b_call.lhs = lhs;
    term->data.b_call.rhs = rhs;

    return term;
}

extern LambdaTerm
if_then_else(
    const restrict LambdaTerm condition,
    const restrict LambdaTerm if_then,
    const restrict LambdaTerm if_else) {
    assert(condition);
    assert(if_then), assert(if_else);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_IF_THEN_ELSE;
    term->data.ite.condition = condition;
    term->data.ite.if_then = if_then;
    term->data.ite.if_else = if_else;

    return term;
}

extern LambdaTerm
fix(const restrict LambdaTerm f) {
    assert(f);

    struct lambda_term *const term = xmalloc(sizeof *term);
    term->ty = LAMBDA_TERM_FIX;
    term->data.fix.f = f;

    return term;
}

// Conversion from a lambda term
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_PURE COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1, 2) //
static uint64_t
count_binder_usage(
    const struct lambda_term *const restrict term,
    const struct lambda_data *const restrict lambda) {
    assert(term);
    assert(lambda);

    switch (term->ty) {
    case LAMBDA_TERM_APPLICATOR:
        return count_binder_usage(term->data.applicator.rator, lambda) +
               count_binder_usage(term->data.applicator.rand, lambda);
    case LAMBDA_TERM_LAMBDA:
        return count_binder_usage(term->data.lambda.body, lambda);
    case LAMBDA_TERM_VAR: {
        struct lambda_data *this_lambda = term->data.var;
        XASSERT(this_lambda);

        return lambda == this_lambda ? true : false;
    }
    case LAMBDA_TERM_CELL: return 0;
    case LAMBDA_TERM_UNARY_CALL:
        return count_binder_usage(term->data.u_call.rand, lambda);
    case LAMBDA_TERM_BINARY_CALL:
        return count_binder_usage(term->data.b_call.lhs, lambda) +
               count_binder_usage(term->data.b_call.rhs, lambda);
    case LAMBDA_TERM_IF_THEN_ELSE:
        return count_binder_usage(term->data.ite.condition, lambda) +
               count_binder_usage(term->data.ite.if_then, lambda) +
               count_binder_usage(term->data.ite.if_else, lambda);
    case LAMBDA_TERM_FIX: //
        return count_binder_usage(term->data.fix.f, lambda);
    default: COMPILER_UNREACHABLE();
    }
}

COMPILER_RETURNS_NONNULL COMPILER_WARN_UNUSED_RESULT COMPILER_NONNULL(1, 2) //
static uint64_t *
build_delimiter_sequence(
    struct context *const restrict graph,
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
    struct context *const restrict graph,
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

COMPILER_NONNULL(1, 2, 3) //
static void
of_lambda_term(
    struct context *const restrict graph,
    struct lambda_term *const restrict term,
    uint64_t *const restrict output_port,
    const uint64_t lvl) {
    assert(graph);
    assert(term);
    assert(output_port);

    switch (term->ty) {
    case LAMBDA_TERM_APPLICATOR: {
        struct lambda_term *const rator = term->data.applicator.rator, //
            *const rand = term->data.applicator.rand;
        XASSERT(rator), XASSERT(rand);

        const struct node applicator = alloc_node(graph, SYMBOL_APPLICATOR);
        connect_ports(&applicator.ports[1], output_port);
        of_lambda_term(graph, rator, &applicator.ports[0], lvl);
        of_lambda_term(graph, rand, &applicator.ports[2], lvl);

        break;
    }
    case LAMBDA_TERM_LAMBDA: {
        struct lambda_data *const tlambda = &term->data.lambda;
        struct lambda_term *const body = term->data.lambda.body;
        XASSERT(tlambda);
        XASSERT(body);

        const struct node lambda = alloc_node(graph, SYMBOL_LAMBDA);
        connect_ports(&lambda.ports[0], output_port);
        const uint64_t nvars = count_binder_usage(body, tlambda);
        uint64_t **dup_ports = NULL;
        if (0 == nvars) {
            const struct node eraser = alloc_node(graph, SYMBOL_ERASER);
            connect_ports(&lambda.ports[1], &eraser.ports[0]);
        } else {
            dup_ports = build_duplicator_tree(graph, &lambda.ports[1], nvars);
        }
        tlambda->dup_ports = dup_ports;
        tlambda->lvl = lvl;
        of_lambda_term(graph, body, &lambda.ports[2], lvl + 1);

        free(dup_ports);

        break;
    }
    case LAMBDA_TERM_VAR: {
        struct lambda_data *const lambda = term->data.var;
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
        const uint64_t value = term->data.cell;

        const struct node cell = alloc_node(graph, SYMBOL_CELL);
        connect_ports(&cell.ports[0], output_port);
        cell.ports[1] = value;

        break;
    }
    case LAMBDA_TERM_UNARY_CALL: {
        uint64_t (*const function)(uint64_t) = term->data.u_call.function;
        struct lambda_term *const rand = term->data.u_call.rand;
        XASSERT(function);
        XASSERT(rand);

        const struct node call = alloc_node(graph, SYMBOL_UNARY_CALL);
        connect_ports(&call.ports[1], output_port);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
        call.ports[2] = U64_OF_FUNCTION(function);
#pragma GCC diagnostic pop
        of_lambda_term(graph, rand, &call.ports[0], lvl);

        break;
    }
    case LAMBDA_TERM_BINARY_CALL: {
        uint64_t (*const function)(uint64_t, uint64_t) = //
            term->data.b_call.function;
        struct lambda_term *const lhs = term->data.b_call.lhs, //
            *const rhs = term->data.b_call.rhs;
        XASSERT(function);
        XASSERT(lhs), XASSERT(rhs);

        const struct node call = alloc_node(graph, SYMBOL_BINARY_CALL);
        connect_ports(&call.ports[1], output_port);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
        call.ports[3] = U64_OF_FUNCTION(function);
#pragma GCC diagnostic pop
        of_lambda_term(graph, lhs, &call.ports[0], lvl);
        of_lambda_term(graph, rhs, &call.ports[2], lvl);

        break;
    }
    case LAMBDA_TERM_IF_THEN_ELSE: {
        struct lambda_term *const condition = term->data.ite.condition, //
            *const if_then = term->data.ite.if_then,                    //
                *const if_else = term->data.ite.if_else;
        XASSERT(condition);
        XASSERT(if_then), XASSERT(if_else);

        const struct node ite = alloc_node(graph, SYMBOL_IF_THEN_ELSE);
        connect_ports(&ite.ports[1], output_port);
        of_lambda_term(graph, condition, &ite.ports[0], lvl);
        of_lambda_term(graph, if_then, &ite.ports[3], lvl);
        of_lambda_term(graph, if_else, &ite.ports[2], lvl);

        break;
    }
    case LAMBDA_TERM_FIX: {
        struct lambda_term *const f = term->data.fix.f;
        XASSERT(f);

        const struct node fix = alloc_node(graph, SYMBOL_FIX);
        connect_ports(&fix.ports[1], output_port);
        of_lambda_term(graph, f, &fix.ports[0], lvl);

        break;
    }

    default: COMPILER_UNREACHABLE();
    }

    // This function takes ownership of the whole `term` object.
    free(term);
}

// The complete algorithm
// @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

COMPILER_NONNULL(1) //
static void
populate_multifocuses(struct context *const restrict graph) {
    assert(graph);

    graph->phase = PHASE_FULL_REDUCTION;

    CONSUME_LIST (
        iter,
        iterate_nodes(graph, SYMBOL_FULL_RANGE /* excluding the root node */)) {
        const struct node f = iter->node;
        XASSERT(f.ports);
        debug("%s(%s)", __func__, print_node(f));

        const struct node g = follow_port(&f.ports[0]);
        XASSERT(g.ports);

        if (is_interacting_with(f, g) && compare_node_ptrs(f, g) < 0 &&
            SYMBOL_ROOT != g.ports[-1]) {
            register_active_pair(graph, f, g);
        }
    }
}

COMPILER_NONNULL(1) //
static void
normalize_x_rules(struct context *const restrict graph) {
    debug("%s()", __func__);

    assert(graph);

    do {
        if (graph->phase >= PHASE_UNWIND) { goto auxiliary_rules; }

        // clang-format off
        CONSUME_MULTIFOCUS (graph->betas, f) { interact(graph, beta, f); }
        CONSUME_MULTIFOCUS (graph->unary_calls, f) { interact(graph, do_unary_call, f); }
        CONSUME_MULTIFOCUS (graph->binary_calls, f) { interact(graph, do_binary_call, f); }
        CONSUME_MULTIFOCUS (graph->binary_calls_aux, f) { interact(graph, do_binary_call_aux, f); }
        CONSUME_MULTIFOCUS (graph->if_then_elses, f) { interact(graph, do_if_then_else, f); }
        CONSUME_MULTIFOCUS (graph->fixpoints, f) { interact(graph, do_fix, f); }
        // clang-format on

    auxiliary_rules:
        // clang-format off
        CONSUME_MULTIFOCUS (graph->annihilations, f) { interact(graph, annihilate, f); }
        CONSUME_MULTIFOCUS (graph->commutations, f) { interact(graph, commute, f); }
        // clang-format on
    } while (!is_normalized_graph(graph));
}

COMPILER_NONNULL(1) COMPILER_HOT //
static void
choose_rule(
    struct context *const restrict graph,
    const struct node f,
    const struct node g) {
    assert(graph);
    XASSERT(f.ports), XASSERT(g.ports);
    assert(is_interaction(f, g));

#define BETA(f, g)            beta(graph, f, g)
#define UNARY_CALL(f, g)      do_unary_call(graph, f, g)
#define BINARY_CALL(f, g)     do_binary_call(graph, f, g)
#define BINARY_CALL_AUX(f, g) do_binary_call_aux(graph, f, g)
#define IF_THEN_ELSE(f, g)    do_if_then_else(graph, f, g)
#define FIX(f, g)             do_fix(graph, f, g)
#define ANNIHILATE(f, g)      annihilate(graph, f, g)
#define COMMUTE(f, g)         commute(graph, f, g)

    DISPATCH_ACTIVE_PAIR(f, g);

#undef COMMUTE
#undef ANNIHILATE
#undef FIX
#undef IF_THEN_ELSE
#undef BINARY_CALL_AUX
#undef BINARY_CALL
#undef UNARY_CALL
#undef BETA

    free_node(f), free_node(g);
}

COMPILER_NONNULL(1) //
static void
weak_reduction(struct context *const restrict graph) {
    assert(graph);

    struct node apex = graph->root;
    struct multifocus *stack = xcalloc(1, sizeof *stack);

rescan:;
    struct node f = follow_port(&apex.ports[1]);

    // clang-format off
#define TRANSITION(condition, action, if_then, if_else) \
    do { if (condition) { action; goto if_then; } else { goto if_else; } } while (false)
    // clang-format on

progress:
    XASSERT(f.ports != apex.ports);

    uint64_t *const target_port = DECODE_ADDRESS(f.ports[0]);

    const struct node g = node_of_port(target_port);

    if (is_interacting_with(f, g)) {
        choose_rule(graph, f, g);
        TRANSITION(stack->count > 0, f = unfocus(stack), progress, rescan);
    }

    if (target_port == &apex.ports[1]) {
        TRANSITION(IS_DELIMITER(f.ports[-1]), apex = f, rescan, finish);
    }

    focus_on(stack, f), f = g;
    goto progress;

#undef TRANSITION

finish:
    free(stack);
}

extern void
optiscope_algorithm(
    FILE *const restrict stream,            // if `NULL`, do not read back
    struct lambda_term *const restrict term // must not be `NULL`
) {
    debug("%s()", __func__);

    assert(term);

    struct context *const graph = alloc_context();

    of_lambda_term(graph, term, &graph->root.ports[1], 0);

    // Phase #1: weak reduction.
    {
        graphviz(graph, "target/1-initial.dot");
        weak_reduction(graph);
        graphviz(graph, "target/1-weakly-reduced.dot");
    }

    if (NULL == stream) { goto finish; }

#define X(focus_name) graph->focus_name = xcalloc(1, sizeof *graph->focus_name);
    CONTEXT_MULTIFOCUSES
#undef X

    // Phase #2: full reduction.
    {
        populate_multifocuses(graph);
        normalize_x_rules(graph);
        graphviz(graph, "target/2-fully-reduced.dot");
    }

    // Phase #3: unwind.
    {
        unwind(graph);
        graphviz(graph, "target/3-unwound.dot");
        normalize_x_rules(graph);
        graphviz(graph, "target/3-unwoundx.dot");
    }

    // Phase #4: scope remove.
    {
        scope_remove(graph);
        graphviz(graph, "target/4-unscoped.dot");
        normalize_x_rules(graph);
        graphviz(graph, "target/4-unscopedx.dot");
    }

    // Phase #5: loop cut.
    {
        loop_cut(graph);
        graphviz(graph, "target/5-unlooped.dot");
        normalize_x_rules(graph);
        graphviz(graph, "target/5-unloopedx.dot");
    }

    assert(is_normalized_graph(graph));

    to_lambda_string(stream, 0, follow_port(&graph->root.ports[1]));

finish:
    print_stats(graph);
    free_context(graph);
}
