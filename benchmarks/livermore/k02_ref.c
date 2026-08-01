/* K2 — ICCG excerpt (Livermore Loop 2) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double x[1001], v[1001];

int main(void) {
    int k, i, ii, ipnt, ipntp, n = 101, rep;

    signel(x, 1001);
    signel(v, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* reset x each rep so results don't blow up */
        signel(x, 1001);

        ii = n;
        ipntp = 0;
        do {
            ipnt = ipntp;
            ipntp += ii;
            ii /= 2;
            i = ipntp - 1;
            for (k = ipnt + 1; k < ipntp; k = k + 2) {
                i++;
                x[i] = x[k] - v[k] * x[k - 1] - v[k + 1] * x[k + 1];
            }
        } while (ii > 0);
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K2 ICCG: x[0] = %.15e\n", x[0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
