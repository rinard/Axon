/* K8 — ADI integration (Livermore Loop 8) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double u1[2][101][5], u2[2][101][5], u3[2][101][5];
static double du1[101], du2[101], du3[101];

int main(void) {
    int kx, ky, nl1, nl2, n = 100, rep;
    double spacer[39]; signel(spacer, 39);
    double a11 = spacer[0], a12 = spacer[1], a13 = spacer[2];
    double a21 = spacer[3], a22 = spacer[4], a23 = spacer[5];
    double a31 = spacer[6], a32 = spacer[7], a33 = spacer[8];
    double sig = spacer[33];

    signel((double *)u1, 2 * 101 * 5);
    signel((double *)u2, 2 * 101 * 5);
    signel((double *)u3, 2 * 101 * 5);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        nl1 = 0; nl2 = 1;
        for (kx = 1; kx < 3; kx++) {
            for (ky = 1; ky < n - 1; ky++) {
                du1[ky] = u1[nl1][ky + 1][kx] - u1[nl1][ky - 1][kx];
                du2[ky] = u2[nl1][ky + 1][kx] - u2[nl1][ky - 1][kx];
                du3[ky] = u3[nl1][ky + 1][kx] - u3[nl1][ky - 1][kx];
                u1[nl2][ky][kx] = u1[nl1][ky][kx] + a11 * du1[ky] + a12 * du2[ky] + a13 * du3[ky]
                    + sig * (u1[nl1][ky][kx + 1] - 2.0 * u1[nl1][ky][kx] + u1[nl1][ky][kx - 1]);
                u2[nl2][ky][kx] = u2[nl1][ky][kx] + a21 * du1[ky] + a22 * du2[ky] + a23 * du3[ky]
                    + sig * (u2[nl1][ky][kx + 1] - 2.0 * u2[nl1][ky][kx] + u2[nl1][ky][kx - 1]);
                u3[nl2][ky][kx] = u3[nl1][ky][kx] + a31 * du1[ky] + a32 * du2[ky] + a33 * du3[ky]
                    + sig * (u3[nl1][ky][kx + 1] - 2.0 * u3[nl1][ky][kx] + u3[nl1][ky][kx - 1]);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K8 ADI: u1[1][50][1] = %.15e\n", u1[1][50][1]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
