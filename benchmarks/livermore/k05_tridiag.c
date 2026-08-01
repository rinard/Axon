/* K5 — Tri-diagonal elimination (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1001), Y(1001), Z(1001), N=1001
   DO I=2,N: X(I) = Z(I)*(Y(I) - X(I-1)) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 7770000

int main(void) {
    double x[1002], y[1002], z[1002];

    signel(x+1, 1001);
    signel(y+1, 1001);
    signel(z+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        signel(x+1, 1001);
        for (long i = 2; i <= N; i++) {
            x[i] = z[i] * (y[i] - x[i-1]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[501] = %f\n", x[501]);
    return 0;
}
