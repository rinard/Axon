/* K1 — Hydro fragment (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1001), Y(1001), Z(1012)
   DO K=1,N: X(K) = Q + Y(K)*(R*Z(K+10) + T*Z(K+11)) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 26147000

int main(void) {
    double x[1002], y[1002], z[1013];
    double spacer[40]; signel(spacer+1, 39);
    double q = spacer[28], r = spacer[30], t = spacer[36];

    signel(y+1, 1001);
    signel(z+1, 1012);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            x[k] = q + y[k] * (r * z[k+10] + t * z[k+11]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[1] = %f\n", x[1]);
    return 0;
}
