/* K21 — Matrix*Matrix Product (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION PX(25,101), VY(101,25), CX(25,101), N=101
   DO K=1,25: DO I=1,25: DO J=1,N: PX(I,J) = PX(I,J) + VY(K,I)*CX(K,J)
   Column-major:
     PX(I,J) dims (25,101): flat (J-1)*25 + I
     VY(K,I) dims (101,25): flat (I-1)*101 + K
     CX(K,J) dims (25,101): flat (J-1)*25 + K */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NJ    101
#define NK    25
#define NREPS 2476000

/* 1-based column-major flat access */
#define PX(i,j) px[((j)-1)*25 + (i)]
#define VY(k,i) vy[((i)-1)*101 + (k)]
#define CX(k,j) cx[((j)-1)*25 + (k)]

int main(void) {
    /* PX: 25*101=2525, max index 2525, need [2526] */
    /* VY: 101*25=2525, need [2526] */
    /* CX: 25*101=2525, need [2526] */
    double px[2526], vy[2526], cx[2526];

    /* Zero PX */
    for (long i = 1; i <= 25*101; i++) px[i] = 0.0;
    /* Init CX and VY */
    signel(&cx[1], 25 * 101);
    signel(&vy[1], 101 * 25);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        /* Reset PX */
        for (long j = 1; j <= NJ; j++)
            for (long i = 1; i <= NK; i++)
                PX(i,j) = 0.0;

        for (long k = 1; k <= 25; k++) {
            for (long i = 1; i <= 25; i++) {
                for (long j = 1; j <= NJ; j++) {
                    PX(i,j) = PX(i,j) + VY(k,i) * CX(k,j);
                }
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px(13,51) = %f\n", PX(13,51));
    return 0;
}
