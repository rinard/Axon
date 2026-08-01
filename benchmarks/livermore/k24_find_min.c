/* K24 — Find Location of First Minimum (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1001), N=1001
   X(N/2+1) = -1.0D+10; M=1; DO K=2,N: IF(X(K).LT.X(M)) M=K */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 30595000

int main(void) {
    double x[1002];

    signel(x+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long m = 1;
    for (long rep = 0; rep < NREPS; rep++) {
        x[N/2+1] = -1.0e+10;
        m = 1;
        for (long k = 2; k <= N; k++) {
            if (x[k] < x[m]) m = k;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("m = %ld, x[m] = %f\n", m, x[m]);
    return 0;
}
