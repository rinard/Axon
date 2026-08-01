/* K15 — Casual Fortran (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION VY(101,25), VH(101,7), VF(101,7), VG(101,7), VS(101,7)
   NG=7, NZ=101. DO J=2,NG: DO K=2,NZ
   Column-major: arr(K,J) at flat (J-1)*101 + K (1-based) */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

#define NZ    101
#define NG    7
#define NREPS 4249000

/* 1-based column-major access with first dim 101 */
#define VY(k,j) vy[((j)-1)*101 + (k)]
#define VH(k,j) vh[((j)-1)*101 + (k)]
#define VF(k,j) vf[((j)-1)*101 + (k)]
#define VG(k,j) vg[((j)-1)*101 + (k)]
#define VS(k,j) vs[((j)-1)*101 + (k)]

int main(void) {
    /* VY: 101*25 = 2525, max index 2525, need [2526] */
    double vy[2526];
    /* VH,VF,VG,VS: 101*7 = 707, max index 707, need [708] */
    double vh[708], vf[708], vg[708], vs[708];

    /* Initialise VY */
    signel(&vy[1], 101 * 25);
    /* Initialise VH */
    signel(&vh[1], 101 * 7);
    /* Initialise VF (ensure positive -- used as divisor) */
    signel(&vf[1], 101 * 7);
    for (long j = 1; j <= 7; j++)
        for (long k = 1; k <= 101; k++)
            if (VF(k,j) <= 0.0) VF(k,j) = 0.001;
    /* Initialise VG */
    signel(&vg[1], 101 * 7);
    /* Initialise VS */
    signel(&vs[1], 101 * 7);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double ar, br, r, s, t;
    for (long l = 0; l < NREPS; l++) {
        ar = 0.053; br = 0.073;
        for (long j = 2; j <= NG; j++) {
            for (long k = 2; k <= NZ; k++) {

                if (j >= NG) {
                    VY(k,j) = 0.0;
                    continue;
                }

                if (VH(k,j+1) > VH(k,j)) t = ar; else t = br;

                if (VF(k,j) < VF(k-1,j)) {
                    if (VH(k-1,j) > VH(k-1,j+1)) r = VH(k-1,j); else r = VH(k-1,j+1);
                    s = VF(k-1,j);
                } else {
                    if (VH(k,j) > VH(k,j+1)) r = VH(k,j); else r = VH(k,j+1);
                    s = VF(k,j);
                }

                VY(k,j) = sqrt(VG(k,j)*VG(k,j) + r*r) * t / s;

                if (k >= NZ) {
                    VS(k,j) = 0.0;
                    continue;
                }

                if (VF(k,j) < VF(k,j-1)) {
                    if (VG(k,j-1) > VG(k+1,j-1)) r = VG(k,j-1); else r = VG(k+1,j-1);
                    s = VF(k,j-1);
                    t = br;
                } else {
                    if (VG(k,j) > VG(k+1,j)) r = VG(k,j); else r = VG(k+1,j);
                    s = VF(k,j);
                    t = ar;
                }

                VS(k,j) = sqrt(VH(k,j)*VH(k,j) + r*r) * t / s;
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vy(51,4) = %f\n", VY(51,4));
    return 0;
}
