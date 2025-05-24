#define BENCHMARKS

#include "../tests.c"

static struct lambda_term *
benchmark_term(void) {
    return applicator(
        applicator(y_combinator(), fast_y_fibonacci_function()), cell(15));
}

int
main(void) {
    optiscope_open_pools();
    optiscope_algorithm(NULL, benchmark_term());
    optiscope_close_pools();
}
