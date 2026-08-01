/* K22 — Planckian distribution (Livermore Loop 22) — netlib reference */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

static double u[1001], v[1001], x[1001], y[1001], w[1001];

int main(void) {
    int k, n = 101, rep;
    double spacer[39]; signel(spacer, 39);
    double expmax = spacer[25];

    signel(u, 1001);
    signel(v, 1001);
    /* Ensure v is positive (used as divisor) */
    for (int i = 0; i < 1001; i++) if (v[i] <= 0.0) v[i] = 1.0;
    signel(x, 1001);
    /* Ensure x[k] > 0 so exp(y[k])-1 != 0 */
    for (int i = 0; i < 1001; i++) if (x[i] <= 0.0) x[i] = 0.01;
    for (int i = 0; i < 1001; i++) { y[i] = 0.0; w[i] = 0.0; }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        expmax = 20.0;
        u[n-1] = 0.99*expmax*v[n-1];
        for (k = 0; k < n; k++) {
            y[k] = u[k]/v[k];
            w[k] = x[k]/(exp(y[k]) - 1.0);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K22 planck: w[50] = %.15e\n", w[50]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
