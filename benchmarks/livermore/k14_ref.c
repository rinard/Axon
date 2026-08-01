/* K14 — 1-D PIC (Livermore Loop 14) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double vx[1001], xx[1001], xi[1001], ex1[1001], dex1[1001];
static double ex[1001], dex[1001], grd[1001], rx[1001], rh[2049];
static long ix[1001], ir[1001];

int main(void) {
    int k, n = 1001, rep;
    double spacer[39]; signel(spacer, 39);
    double flx = spacer[26];

    /* grd must be valid grid indices */
    for (int i = 0; i < 1001; i++) grd[i] = (i % 512) + 1.5;
    signel(ex, 1001);
    signel(dex, 1001);
    for (int i = 0; i < 1001; i++) {
        vx[i] = xx[i] = xi[i] = ex1[i] = dex1[i] = rx[i] = 0.0;
        ix[i] = ir[i] = 0;
    }
    for (int i = 0; i < 2049; i++)
        rh[i] = 0.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        for (int i = 0; i < 2049; i++)
            rh[i] = 0.0;

        for (k = 0; k < n; k++) {
            vx[k] = 0.0;
            xx[k] = 0.0;
            ix[k] = (long)grd[k];
            xi[k] = (double)ix[k];
            ex1[k] = ex[ix[k]-1];
            dex1[k] = dex[ix[k]-1];
        }
        for (k = 0; k < n; k++) {
            vx[k] = vx[k] + ex1[k] + (xx[k]-xi[k])*dex1[k];
            xx[k] = xx[k] + vx[k] + flx;
            ir[k] = xx[k];
            rx[k] = xx[k] - ir[k];
            ir[k] = (ir[k] & 2048-1) + 1;
            xx[k] = rx[k] + ir[k];
        }
        for (k = 0; k < n; k++) {
            rh[ir[k]-1] += 1.0 - rx[k];
            rh[ir[k]] += rx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K14 1-D PIC: xx[0] = %.15e\n", xx[0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
