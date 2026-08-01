/* K2 -- ICCG excerpt (canonical, 1-based indexing) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 7500000

int main(void) {
    double x[2051], v[2051];

    signel(v+1, 2050);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        signel(x+1, 2050);
        long ii = N;
        long ipntp = 0;
        do {
            long ipnt = ipntp;
            ipntp = ipntp + ii;
            ii = ii / 2;
            long i = ipntp + 1;
            for (long k = ipnt + 2; k <= ipntp; k += 2) {
                i = i + 1;
                x[i] = x[k] - v[k] * x[k-1] - v[k+1] * x[k+1];
            }
        } while (ii > 1);
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[n] = %f\n", x[N]);
    return 0;
}
