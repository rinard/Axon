/* K6 — General linear recurrence equations (Livermore Loop 6) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double w[1001];
static double b[64][64];

int main(void) {
    int i, k, n = 64, rep;

    signel((double *)b, 64 * 64);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 1000; rep++) {
        /* reset w each rep */
        for (int j = 0; j < 1001; j++)
            w[j] = 0.0;
        w[0] = 0.01;

        for (i = 1; i < n; i++) {
            for (k = 0; k < i; k++) {
                w[i] += b[k][i] * w[(i - k) - 1];
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K6 recurrence: w[63] = %.15e\n", w[63]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
