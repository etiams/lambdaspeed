#define BENCHMARKS

#include "../tests.c"

#include <stdint.h>

static struct lambda_term *
owl_combinator(void) {
    struct lambda_term *a, *b;

    return lambda(a, lambda(b, applicator(var(b), applicator(var(a), var(b)))));
}

static struct lambda_term *
owl_explosion(const uint64_t depth) {
    assert(depth > 0);

    struct lambda_term *result = owl_combinator();

    for (uint64_t i = 1; i < depth; i++) {
        result = applicator(result, owl_combinator());
    }

    return result;
}

int
main(void) {
    optiscope_open_pools();
    struct lambda_term *term =
        applicator(owl_explosion(1000), owl_combinator());
    optiscope_algorithm(NULL, term);
    optiscope_close_pools();
}
