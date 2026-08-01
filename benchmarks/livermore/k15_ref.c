/* K15 — Casual Fortran (Livermore Loop 15) — netlib reference */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

static double vy[25][101], vh[7][101], vf[7][101], vg[7][101], vs[7][101];

int main(void) {
    int j, k, n = 101, ng, nz, rep;
    double ar, br, r, s, t;

    signel((double *)vy, 25 * 101);
    signel((double *)vh, 7 * 101);
    signel((double *)vf, 7 * 101);
    /* Ensure vf is positive (used as divisor) */
    for (int i = 0; i < 7; i++)
        for (int jj = 0; jj < 101; jj++)
            if (vf[i][jj] <= 0.0) vf[i][jj] = 0.001;
    signel((double *)vg, 7 * 101);
    signel((double *)vs, 7 * 101);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        ng = 7; nz = n; ar = 0.053; br = 0.073;
        for (j = 1; j < ng; j++) {
            for (k = 1; k < nz; k++) {
                if ((j+1) >= ng) { vy[j][k] = 0.0; continue; }
                if (vh[j+1][k] > vh[j][k]) t = ar; else t = br;
                if (vf[j][k] < vf[j][k-1]) {
                    if (vh[j][k-1] > vh[j+1][k-1]) r = vh[j][k-1]; else r = vh[j+1][k-1];
                    s = vf[j][k-1];
                } else {
                    if (vh[j][k] > vh[j+1][k]) r = vh[j][k]; else r = vh[j+1][k];
                    s = vf[j][k];
                }
                vy[j][k] = sqrt(vg[j][k]*vg[j][k] + r*r) * t/s;
                if ((k+1) >= nz) { vs[j][k] = 0.0; continue; }
                if (vf[j][k] < vf[j-1][k]) {
                    if (vg[j-1][k] > vg[j-1][k+1]) r = vg[j-1][k]; else r = vg[j-1][k+1];
                    s = vf[j-1][k]; t = br;
                } else {
                    if (vg[j][k] > vg[j][k+1]) r = vg[j][k]; else r = vg[j][k+1];
                    s = vf[j][k]; t = ar;
                }
                vs[j][k] = sqrt(vh[j][k]*vh[j][k] + r*r) * t / s;
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K15 casual: vy[3][50] = %.15e\n", vy[3][50]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
