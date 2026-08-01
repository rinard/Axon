/* K10 -- Difference predictors (canonical, 1-based indexing)
   Canonical: PX(25,101), CX(25,101)
   Column-major: arr(i,j) at flat (j-1)*25 + i (1-based) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 52000000

/* 1-based Fortran column-major: arr(i,j) with dims (25,101) */
#define PX(i,j) px[((j)-1)*25 + (i)]
#define CX(i,j) cx[((j)-1)*25 + (i)]

int main(void) {
    /* Max flat: (101-1)*25 + 25 = 2525, need [2526] */
    double px[2526], cx[2526];

    signel(&px[1], 25 * 101);
    signel(&cx[1], 25 * 101);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            double ar, br, cr;
            ar       =      CX(5,k);
            br       = ar - PX(5,k);
            PX(5,k)  = ar;
            cr       = br - PX(6,k);
            PX(6,k)  = br;
            ar       = cr - PX(7,k);
            PX(7,k)  = cr;
            br       = ar - PX(8,k);
            PX(8,k)  = ar;
            cr       = br - PX(9,k);
            PX(9,k)  = br;
            ar       = cr - PX(10,k);
            PX(10,k) = cr;
            br       = ar - PX(11,k);
            PX(11,k) = ar;
            cr       = br - PX(12,k);
            PX(12,k) = br;
            PX(14,k) = cr - PX(13,k);
            PX(13,k) = cr;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px(14,1) = %f\n", PX(14,1));
    return 0;
}
