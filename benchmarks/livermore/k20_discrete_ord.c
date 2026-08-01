/* K20 — Discrete Ordinates Transport (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1001), Y(1001), Z(1001), W(1001), V(1001),
            U(1001), G(1001), XX(1001), VX(1001)
   N=1000. Re-inits XX each rep. XX(K+1) updated for K=1..N. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1000
#define NREPS 1570000

int main(void) {
    double x[1002], y[1002], z[1002], w[1002], v[1002];
    double u[1002], g[1002], xx[1002], vx[1002];
    double spacer[40]; signel(spacer+1, 39);
    double dk = spacer[15], s = spacer[32], t = spacer[36];

    signel(x+1, 1001);
    signel(y+1, 1001);
    signel(z+1, 1001);
    signel(w+1, 1001);
    signel(v+1, 1001);
    signel(u+1, 1001);
    signel(g+1, 1001);
    signel(xx+1, 1001);
    /* Ensure xx is nonzero divisor */
    for (long i = 1; i <= 1001; i++) xx[i] += 1.0;
    signel(vx+1, 1001);
    /* Ensure vx is nonzero divisor */
    for (long i = 1; i <= 1001; i++) vx[i] += 2.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        /* Re-init XX each rep */
        signel(xx+1, 1001);
        for (long i = 1; i <= 1001; i++) xx[i] += 1.0;

        for (long k = 1; k <= N; k++) {
            double di = y[k] - g[k] / (xx[k] + dk);
            double dn = 0.2;
            if (di != 0.0) {
                dn = z[k] / di;
                if (t < dn) dn = t;
                if (s > dn) dn = s;
            }
            x[k] = ((w[k] + v[k]*dn)*xx[k] + u[k]) / (vx[k] + v[k]*dn);
            xx[k+1] = (x[k] - xx[k])*dn + xx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[1] = %f\n", x[1]);
    return 0;
}
