/* K4 -- Banded linear equations (canonical, 1-based indexing)
   XZ alias of X (extended through Z); treat as single array of length 1201. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 14000000

int main(void) {
    double xz[1202], y[1002];

    signel(y+1, 1001);

    long m = (1001 - 7) / 2;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        signel(xz+1, 1201);
        for (long k = 7; k <= N; k = k + m) {
            long lw = k - 6;
            double temp = xz[k-1];
            for (long j = 5; j <= N; j = j + 5) {
                temp = temp - xz[lw] * y[j];
                lw = lw + 1;
            }
            xz[k-1] = y[5] * temp;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("xz[7] = %f\n", xz[7]);
    return 0;
}
