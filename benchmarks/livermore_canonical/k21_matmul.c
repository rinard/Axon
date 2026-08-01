/* K21 -- Matrix*Matrix Product (canonical, 1-based indexing)
   Canonical body:
     DO 21 k=1,25; DO 21 i=1,25; DO 21 j=1,n:
       PX(i,j) = PX(i,j) + VY(i,k) * CX(k,j)
   Column-major:
     PX dims (25,101): PX(i,j) at flat (j-1)*25 + i
     VY dims (101,25): VY(i,k) at flat (k-1)*101 + i
     CX dims (25,101): CX(k,j) at flat (j-1)*25 + k */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NJ    101
#define NK    25
#define NI    25
#define NREPS 425000

#define PX(i,j) px[((j)-1)*25  + (i)]
#define VY(i,k) vy[((k)-1)*101 + (i)]
#define CX(k,j) cx[((j)-1)*25  + (k)]

int main(void) {
    /* PX:25*101=2525, VY:101*25=2525, CX:25*101=2525 (all need [2526]) */
    double px[2526], vy[2526], cx[2526];

    for (long i = 1; i <= 25*101; i++) px[i] = 0.0;
    /* VY filled column-major: outer k=1..25, inner i=1..101 */
    signel(&vy[1], 101 * 25);
    /* CX filled column-major: outer j=1..101, inner k=1..25 */
    signel(&cx[1], 25 * 101);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= NK; k++) {
            for (long i = 1; i <= NI; i++) {
                for (long j = 1; j <= NJ; j++) {
                    PX(i,j) = PX(i,j) + VY(i,k) * CX(k,j);
                }
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px(1,1) = %f\n", PX(1,1));
    return 0;
}
