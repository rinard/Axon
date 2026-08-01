/* K23 — 2-D implicit hydrodynamics (Livermore Loop 23) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double za[7][101], zr[7][101], zb[7][101];
static double zu[7][101], zv[7][101], zz[7][101];

int main(void) {
    int j, k, n = 100, rep;
    double qa;

    signel((double *)za, 7 * 101);
    signel((double *)zr, 7 * 101);
    signel((double *)zb, 7 * 101);
    signel((double *)zu, 7 * 101);
    signel((double *)zv, 7 * 101);
    signel((double *)zz, 7 * 101);
    /* Scale coefficients for stable relaxation */
    for (int i = 0; i < 7; i++)
        for (int jj = 0; jj < 101; jj++) {
            zr[i][jj] *= 0.1; zb[i][jj] *= 0.1;
            zu[i][jj] *= 0.1; zv[i][jj] *= 0.1;
        }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 100000; rep++) {
        for (j = 1; j < 6; j++) {
            for (k = 1; k < n; k++) {
                qa = za[j+1][k]*zr[j][k] + za[j-1][k]*zb[j][k] +
                     za[j][k+1]*zu[j][k] + za[j][k-1]*zv[j][k] + zz[j][k];
                za[j][k] += 0.175*(qa - za[j][k]);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K23 hydro implicit: za[3][50] = %.15e\n", za[3][50]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
