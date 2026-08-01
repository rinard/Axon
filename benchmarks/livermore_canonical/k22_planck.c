/* K22 -- Planckian Distribution (canonical, 1-based indexing)
   Canonical body:
     EXPMAX = 20.0
     fw = 1.0
     U(n) = 0.99*EXPMAX*V(n)
     DO 22 k=1,n:
       Y(k) = U(k)/V(k)
       W(k) = X(k)/(EXP(Y(k)) - fw) */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 51900000

int main(void) {
    double u[102], v[102], w[102], x[102], y[102];

    signel(u+1, 101);
    signel(v+1, 101);
    signel(x+1, 101);
    /* Ensure v[k] > 0 (used as divisor) */
    for (long k = 1; k <= 101; k++)
        if (v[k] <= 0.0) v[k] = 1.0;
    for (long k = 1; k <= 101; k++) { y[k] = 0.0; w[k] = 0.0; }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double expmax, fw;
    for (long rep = 0; rep < NREPS; rep++) {
        expmax = 20.0;
        fw = 1.0;
        u[N] = 0.99 * expmax * v[N];
        for (long k = 1; k <= N; k++) {
            y[k] = u[k] / v[k];
            w[k] = x[k] / (exp(y[k]) - fw);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("w[51] = %f\n", w[51]);
    return 0;
}
