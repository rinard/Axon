/* K14 -- 1-D Particle in Cell (canonical, 1-based indexing)
   Canonical body: lines 243-264 of the kernels listing.
   MOD2N(IR(k), 2048) = IR(k) & 2047. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 2700000

int main(void) {
    static double vx[1002], xx[1002], xi[1002], ex1[1002], dex1[1002];
    static double ex[1002], dex[1002], grd[1002], rx[1002];
    static double rh[2050];
    static long ix[1002], ir[1002];
    static double spacer[40];

    /* SPACER -> FLX */
    double fuzz = 1.2345e-3, buzz = 1.0 + fuzz, fizz = 1.1 * fuzz;
    for (long k = 1; k <= 39; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        spacer[k] = (buzz - fizz) * 0.1;
    }
    double flx = spacer[27];

    /* GRD */
    for (long i = 1; i <= N; i++)
        grd[i] = (double)((i - 1) % 512) + 1.5;

    /* EX, DEX */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= N; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        ex[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= N; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        dex[k] = (buzz - fizz) * 0.1;
    }

    /* RH */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 2049; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        rh[k] = (buzz - fizz) * 0.1;
    }

    for (long i = 1; i <= N; i++) {
        vx[i] = 0.0; xx[i] = 0.0; xi[i] = 0.0;
        ex1[i] = 0.0; dex1[i] = 0.0; rx[i] = 0.0;
        ix[i] = 0; ir[i] = 0;
    }

    double fw = 1.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 1; rep <= NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            vx[k] = 0.0;
            xx[k] = 0.0;
            ix[k] = (long)grd[k];
            xi[k] = (double)ix[k];
            ex1[k] = ex[ix[k]];
            dex1[k] = dex[ix[k]];
        }
        for (long k = 1; k <= N; k++) {
            vx[k] = vx[k] + ex1[k] + (xx[k] - xi[k]) * dex1[k];
            xx[k] = xx[k] + vx[k] + flx;
            ir[k] = (long)xx[k];
            rx[k] = xx[k] - (double)ir[k];
            ir[k] = (ir[k] & 2047) + 1;
            xx[k] = rx[k] + (double)ir[k];
        }
        for (long k = 1; k <= N; k++) {
            rh[ir[k]]   = rh[ir[k]]   + fw - rx[k];
            rh[ir[k]+1] = rh[ir[k]+1] + rx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("rh(1) = %.15e\n", rh[1]);
    return 0;
}
