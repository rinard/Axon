/* K11 -- First sum / partial sums (canonical, 1-based indexing)
   Canonical body: X(1) = Y(1); DO k=2,n: X(k) = X(k-1) + Y(k) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 34000000

int main(void) {
    double x[1002], y[1002];

    signel(y+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        x[1] = y[1];
        for (long k = 2; k <= N; k++) {
            x[k] = x[k-1] + y[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[n] = %f\n", x[N]);
    return 0;
}
