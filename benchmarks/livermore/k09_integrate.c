/* K9 — Integrate Predictors (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION PX(101,25), N=101
   PX(I,1) = DM28*PX(I,13) + DM27*PX(I,12) + DM26*PX(I,11)
           + DM25*PX(I,10) + DM24*PX(I,9)  + DM23*PX(I,8)
           + DM22*PX(I,7)  + C0*(PX(I,5) + PX(I,6)) + PX(I,3)
   Column-major: PX(I,J) at flat (J-1)*101 + I (1-based) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NCOL  25
#define NREPS 60639000

/* 1-based Fortran column-major: PX(i,j) with dims (101,25) */
#define PX(i,j) px[((j)-1)*101 + (i)]

int main(void) {
    /* Max flat index: (25-1)*101 + 101 = 2525, need [2526] */
    double px[2526];
    double spacer[40]; signel(spacer+1, 39);
    double dm28 = spacer[22], dm27 = spacer[21], dm26 = spacer[20];
    double dm25 = spacer[19], dm24 = spacer[18], dm23 = spacer[17];
    double dm22 = spacer[16], c0 = spacer[12];

    /* Initialise: fill 101*25=2525 elements starting at index 1 */
    signel(&px[1], 101 * 25);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long l = 0; l < NREPS; l++) {
        for (long i = 1; i <= N; i++) {
            PX(i,1) = dm28*PX(i,13) + dm27*PX(i,12)
                     + dm26*PX(i,11) + dm25*PX(i,10)
                     + dm24*PX(i,9)  + dm23*PX(i,8)
                     + dm22*PX(i,7)  + c0*(PX(i,5) + PX(i,6))
                     + PX(i,3);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px(51,1) = %f\n", PX(51,1));
    return 0;
}
