#define BENCHMARKS

#include "../tests.c"

static struct lambda_term *
church_ten(void) {
    return applicator(
        applicator(church_multiply(), church_five()), church_two());
}

static struct lambda_term *
church_twenty(void) {
    return applicator(
        applicator(church_multiply(), church_ten()), church_two());
}

int
main(void) {
    lambdaspeed_open_pools();
    lambdaspeed_algorithm(NULL, applicator(factorial_term(), church_twenty()));
    lambdaspeed_close_pools();
}
