/* K10 — Difference Predictors (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION PX(101,25), CX(101,25), N=101
   Column-major: PX(I,J) at flat (J-1)*101 + I (1-based) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NCOL  25
#define NREPS 48656000

/* 1-based Fortran column-major: arr(i,j) with dims (101,25) */
#define PX(i,j) px[((j)-1)*101 + (i)]
#define CX(i,j) cx[((j)-1)*101 + (i)]

int main(void) {
    /* Max flat index: (25-1)*101 + 101 = 2525, need [2526] */
    double px[2526], cx[2526];

    /* Initialise */
    signel(&px[1], 101 * 25);
    signel(&cx[1], 101 * 25);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long l = 0; l < NREPS; l++) {
        for (long i = 1; i <= N; i++) {
            double ar, br, cr;
            ar       =      CX(i,5);
            br       = ar - PX(i,5);
            PX(i,5)  = ar;
            cr       = br - PX(i,6);
            PX(i,6)  = br;
            ar       = cr - PX(i,7);
            PX(i,7)  = cr;
            br       = ar - PX(i,8);
            PX(i,8)  = ar;
            cr       = br - PX(i,9);
            PX(i,9)  = br;
            ar       = cr - PX(i,10);
            PX(i,10) = cr;
            br       = ar - PX(i,11);
            PX(i,11) = ar;
            cr       = br - PX(i,12);
            PX(i,12) = br;
            PX(i,14) = cr - PX(i,13);
            PX(i,13) = cr;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px(51,5) = %f\n", PX(51,5));
    return 0;
}
