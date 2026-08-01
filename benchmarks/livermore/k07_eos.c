/* K7 — Equation of state fragment (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1001), U(1001), Z(1001), Y(1001), N=995
   DO K=1,N: X(K) = U(K) + R*(Z(K)+R*Y(K))
                   + T*(U(K+3)+R*(U(K+2)+R*U(K+1))
                   + T*(U(K+6)+Q*(U(K+5)+Q*U(K+4)))) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     995
#define NREPS 11472000

int main(void) {
    double x[1002], y[1002], z[1002], u[1008];
    double spacer[40]; signel(spacer+1, 39);
    double q = spacer[28], r = spacer[30], t = spacer[36];

    signel(y+1, 1001);
    signel(z+1, 1001);
    signel(u+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            x[k] = u[k] + r*(z[k] + r*y[k]) +
                   t*(u[k+3] + r*(u[k+2] + r*u[k+1]) +
                      t*(u[k+6] + q*(u[k+5] + q*u[k+4])));
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[1] = %f\n", x[1]);
    return 0;
}
