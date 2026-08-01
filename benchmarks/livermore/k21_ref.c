/* K21 — Matrix*matrix product (Livermore Loop 21) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double px[101][25], vy[25][101], cx[101][25];

int main(void) {
    int i, j, k, n = 101, rep;

    for (int ii = 0; ii < 101; ii++)
        for (int jj = 0; jj < 25; jj++)
            px[ii][jj] = 0.0;
    signel((double *)cx, 101 * 25);
    signel((double *)vy, 25 * 101);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        for (int ii = 0; ii < 101; ii++)
            for (int jj = 0; jj < 25; jj++)
                px[ii][jj] = 0.0;

        for (k = 0; k < 25; k++) {
            for (i = 0; i < 25; i++) {
                for (j = 0; j < n; j++) {
                    px[j][i] += vy[k][i] * cx[j][k];
                }
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K21 matmul: px[50][12] = %.15e\n", px[50][12]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
