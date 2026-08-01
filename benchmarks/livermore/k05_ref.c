/* K5 — Tri-diagonal elimination (Livermore Loop 5) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double x[1001], y[1001], z[1001];

int main(void) {
    int i, n = 1001, rep;

    signel(x, 1001);
    signel(y, 1001);
    signel(z, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* reset x each rep */
        signel(x, 1001);

        for (i = 1; i < n; i++) {
            x[i] = z[i] * (y[i] - x[i - 1]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K5 tridiag: x[500] = %.15e\n", x[500]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
