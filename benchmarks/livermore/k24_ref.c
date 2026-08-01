/* K24 — Find location of first minimum in array (Livermore Loop 24) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double x[1001];

int main(void) {
    int k, m, n = 1001, rep;

    signel(x, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        x[n/2] = -1.0e+10;
        m = 0;
        for (k = 1; k < n; k++) {
            if (x[k] < x[m]) m = k;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K24 find min: m = %d, x[m] = %.15e\n", m, x[m]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
