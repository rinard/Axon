/* K12 — First difference (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1001), Y(1001), N=1000
   DO K=1,N: X(K) = Y(K+1) - Y(K) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1000
#define NREPS 35622000

int main(void) {
    double x[1002], y[1002];

    signel(y+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            x[k] = y[k+1] - y[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[1] = %f\n", x[1]);
    return 0;
}
