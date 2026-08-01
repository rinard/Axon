/* K18 — 2-D explicit hydrodynamics (Livermore Loop 18) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double za[7][101], zp[7][101], zq[7][101], zr[7][101];
static double zm[7][101], zb[7][101], zu[7][101], zv[7][101], zz[7][101];

int main(void) {
    int j, k, kn, jn, n = 100, rep;
    double t, s;

    signel((double *)zp, 7 * 101);
    signel((double *)zq, 7 * 101);
    signel((double *)zr, 7 * 101);
    signel((double *)zm, 7 * 101);
    /* Ensure zm is large enough to damp division */
    for (int i = 0; i < 7; i++)
        for (int jj = 0; jj < 101; jj++)
            zm[i][jj] += 10.0;
    signel((double *)zz, 7 * 101);
    for (int i = 0; i < 7; i++)
        for (int jj = 0; jj < 101; jj++) {
            za[i][jj] = 0.0;
            zb[i][jj] = 0.0;
            zu[i][jj] = 0.0;
            zv[i][jj] = 0.0;
        }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        t = 0.0037; s = 0.0041; kn = 6; jn = 100; /* jn=100 for safety: j+1 up to 100 */
        for (k = 1; k < kn; k++) {
          for (j = 1; j < jn; j++) {
              za[k][j] = (zp[k+1][j-1]+zq[k+1][j-1]-zp[k][j-1]-zq[k][j-1])*(zr[k][j]+zr[k][j-1])/(zm[k][j-1]+zm[k+1][j-1]);
              zb[k][j] = (zp[k][j-1]+zq[k][j-1]-zp[k][j]-zq[k][j])*(zr[k][j]+zr[k-1][j])/(zm[k][j]+zm[k][j-1]);
          }
        }
        for (k = 1; k < kn; k++) {
            for (j = 1; j < jn; j++) {
                zu[k][j] += s*(za[k][j]*(zz[k][j]-zz[k][j+1]) - za[k][j-1]*(zz[k][j]-zz[k][j-1])
                              - zb[k][j]*(zz[k][j]-zz[k-1][j]) + zb[k+1][j]*(zz[k][j]-zz[k+1][j]));
                zv[k][j] += s*(za[k][j]*(zr[k][j]-zr[k][j+1]) - za[k][j-1]*(zr[k][j]-zr[k][j-1])
                              - zb[k][j]*(zr[k][j]-zr[k-1][j]) + zb[k+1][j]*(zr[k][j]-zr[k+1][j]));
            }
        }
        for (k = 1; k < kn; k++) {
            for (j = 1; j < jn; j++) {
                zr[k][j] += t*zu[k][j];
                zz[k][j] += t*zv[k][j];
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K18 hydro 2D: zu[3][50] = %.15e\n", zu[3][50]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
