/* K3 — Inner product (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION Z(1001), X(1001), N=1001
   DO K=1,N: Q = Q + Z(K)*X(K) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 31726000

int main(void) {
    double x[1002], z[1002];

    signel(z+1, 1001);
    signel(x+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double q = 0.0;
    for (long rep = 0; rep < NREPS; rep++) {
        q = 0.0;
        for (long k = 1; k <= N; k++) {
            q = q + z[k] * x[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("q = %f\n", q);
    return 0;
}
