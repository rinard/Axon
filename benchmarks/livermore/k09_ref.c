/* K9 — Integrate predictors (Livermore Loop 9) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double px[101][25];

int main(void) {
    int i, n = 101, rep;
    double spacer[39]; signel(spacer, 39);
    double dm22 = spacer[15], dm23 = spacer[16], dm24 = spacer[17], dm25 = spacer[18];
    double dm26 = spacer[19], dm27 = spacer[20], dm28 = spacer[21], c0 = spacer[11];

    signel((double *)px, 101 * 25);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        for (i = 0; i < n; i++) {
            px[i][0] = dm28 * px[i][12] + dm27 * px[i][11] + dm26 * px[i][10] +
                       dm25 * px[i][9] + dm24 * px[i][8] + dm23 * px[i][7] +
                       dm22 * px[i][6] + c0 * (px[i][4] + px[i][5]) + px[i][2];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K9 integrate pred: px[50][0] = %.15e\n", px[50][0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
