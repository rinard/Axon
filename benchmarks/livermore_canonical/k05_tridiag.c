/* K5 -- Tri-diagonal elimination (canonical, 1-based indexing)
   Canonical body: DO i=2,n: X(i) = Z(i)*(Y(i) - X(i-1)) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 9700000

int main(void) {
    double x[1002], y[1002], z[1002];

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
    printf("x[n] = %f\n", x[N]);
    return 0;
}
