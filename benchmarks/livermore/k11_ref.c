/* K11 — First sum (Livermore Loop 11) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double x[1001], y[1001];

int main(void) {
    int k, n = 1001, rep;

    signel(y, 1001);
    for (int i = 0; i < 1001; i++) x[i] = 0.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        x[0] = y[0];
        for (k = 1; k < n; k++) {
            x[k] = x[k - 1] + y[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K11 first sum: x[1000] = %.15e\n", x[1000]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
