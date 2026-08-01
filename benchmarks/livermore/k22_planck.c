/* K22 — Planckian Distribution (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION U(1001), V(1001), X(1001), Y(1001), W(1001), N=101
   U(N) = 0.99*EXPMAX*V(N)
   DO K=1,N: Y(K) = U(K)/V(K); W(K) = X(K)/(DEXP(Y(K))-1.0) */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 48640000

int main(void) {
    double u[1002], v[1002], x[1002], y[1002], w[1002];

    signel(u+1, 1001);
    signel(v+1, 1001);
    signel(x+1, 1001);
    /* Ensure v[k] > 0 (used as divisor) */
    for (long k = 1; k <= 1001; k++)
        if (v[k] <= 0.0) v[k] = 1.0;
    /* Ensure x[k] > 0 for exp-1 divisor */
    for (long k = 1; k <= 1001; k++)
        if (x[k] <= 0.0) x[k] = 0.01;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double expmax;
    for (long rep = 0; rep < NREPS; rep++) {
        expmax = 20.0;
        u[N] = 0.99 * expmax * v[N];
        for (long k = 1; k <= N; k++) {
            y[k] = u[k] / v[k];
            w[k] = x[k] / (exp(y[k]) - 1.0);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("w[51] = %f\n", w[51]);
    return 0;
}
