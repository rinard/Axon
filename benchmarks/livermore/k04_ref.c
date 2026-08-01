/* K4 — Banded linear equations (Livermore Loop 4) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double x[1001], y[1001];

int main(void) {
    int k, j, lw, m, n = 1001, rep;
    double temp;

    signel(x, 1001);
    signel(y, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* reset x each rep */
        signel(x, 1001);

        m = (1001 - 7) / 2;
        for (k = 6; k < 1001; k = k + m) {
            lw = k - 6;
            temp = x[k - 1];
            for (j = 4; j < n; j = j + 5) {
                temp -= x[lw] * y[j];
                lw++;
            }
            x[k - 1] = y[4] * temp;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K4 banded: x[5] = %.15e\n", x[5]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
