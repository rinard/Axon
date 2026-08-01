/* K9 -- Integrate predictors (canonical, 1-based indexing)
   Canonical: PX(25,101) -- first index (25) is fast.
     PX(1,k) = DM28*PX(13,k) + DM27*PX(12,k) + DM26*PX(11,k)
             + DM25*PX(10,k) + DM24*PX(9,k)  + DM23*PX(8,k)
             + DM22*PX(7,k)  + C0*(PX(5,k) + PX(6,k)) + PX(3,k)
   Column-major: PX(i,j) at flat (j-1)*25 + i (1-based) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 77700000

/* 1-based Fortran column-major: PX(i,j) with dims (25,101) */
#define PX(i,j) px[((j)-1)*25 + (i)]

int main(void) {
    /* Max flat: (101-1)*25 + 25 = 2525, need [2526] */
    double px[2526];
    double spacer[40];

    signel(spacer+1, 39);
    double c0   = spacer[12];
    double dm22 = spacer[16], dm23 = spacer[17], dm24 = spacer[18];
    double dm25 = spacer[19], dm26 = spacer[20], dm27 = spacer[21];
    double dm28 = spacer[22];

    /* Fill 25*101=2525 elements starting at index 1 */
    signel(&px[1], 25 * 101);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            PX(1,k) = dm28*PX(13,k) + dm27*PX(12,k)
                    + dm26*PX(11,k) + dm25*PX(10,k)
                    + dm24*PX(9,k)  + dm23*PX(8,k)
                    + dm22*PX(7,k)
                    + c0*(PX(5,k) + PX(6,k))
                    + PX(3,k);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px(1,1) = %f\n", PX(1,1));
    return 0;
}
