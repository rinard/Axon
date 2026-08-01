/* K7 — Equation of state fragment (Livermore Loop 7) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double x[1001], u[1001], z[1001], y[1001];

int main(void) {
    int k, n = 995, rep;
    double spacer[39]; signel(spacer, 39);
    double q = spacer[27], r = spacer[29], t = spacer[35];

    signel(u, 1001);
    signel(z, 1001);
    signel(y, 1001);
    for (int i = 0; i < 1001; i++) x[i] = 0.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        for (k = 0; k < n; k++) {
            x[k] = u[k] + r * (z[k] + r * y[k]) +
                   t * (u[k + 3] + r * (u[k + 2] + r * u[k + 1]) +
                        t * (u[k + 6] + q * (u[k + 5] + q * u[k + 4])));
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K7 EOS: x[0] = %.15e\n", x[0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
