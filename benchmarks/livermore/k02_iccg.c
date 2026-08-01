/* K2 — ICCG excerpt (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1001), V(1001), N=101
   Halving do-while with stride-2 inner loop */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 11495000

int main(void) {
    double x[1002], v[1002];

    signel(x+1, 1001);
    signel(v+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        signel(x+1, 1001);
        long ii = N;
        long ipntp = 0;
        do {
            long ipnt = ipntp;
            ipntp = ipntp + ii;
            ii = ii / 2;
            long i = ipntp;
            for (long k = ipnt + 2; k <= ipntp; k += 2) {
                i = i + 1;
                x[i] = x[k] - v[k] * x[k-1] - v[k+1] * x[k+1];
            }
        } while (ii > 0);
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[1] = %f\n", x[1]);
    return 0;
}
