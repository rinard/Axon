/* K10 — Difference predictors (Livermore Loop 10) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double px[101][25], cx[101][25];

int main(void) {
    int i, n = 101, rep;
    double ar, br, cr;

    signel((double *)px, 101 * 25);
    signel((double *)cx, 101 * 25);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        for (i = 0; i < n; i++) {
            ar       =     cx[i][4];
            br       = ar - px[i][4];
            px[i][4] = ar;
            cr       = br - px[i][5];
            px[i][5] = br;
            ar       = cr - px[i][6];
            px[i][6] = cr;
            br       = ar - px[i][7];
            px[i][7] = ar;
            cr       = br - px[i][8];
            px[i][8] = br;
            ar       = cr - px[i][9];
            px[i][9] = cr;
            br       = ar - px[i][10];
            px[i][10] = ar;
            cr       = br - px[i][11];
            px[i][11] = br;
            px[i][13] = cr - px[i][12];
            px[i][12] = cr;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K10 diff pred: px[50][4] = %.15e\n", px[50][4]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
