/* K23 -- 2-D Implicit Hydrodynamics (canonical, 1-based indexing)
   Canonical body:
     fw = 0.175
     DO 23 j=2,6; DO 23 k=2,n:
       QA = ZA(k,j+1)*ZR(k,j) + ZA(k,j-1)*ZB(k,j)
          + ZA(k+1,j)*ZU(k,j) + ZA(k-1,j)*ZV(k,j) + ZZ(k,j)
       ZA(k,j) = ZA(k,j) + fw*(QA - ZA(k,j))
   Column-major: arr(k,j) at flat (j-1)*101 + k */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NTOT  (101 * 7)
#define NREPS 8600000

#define ZA(k,j) za[((j)-1)*101 + (k)]
#define ZB(k,j) zb[((j)-1)*101 + (k)]
#define ZR(k,j) zr[((j)-1)*101 + (k)]
#define ZU(k,j) zu[((j)-1)*101 + (k)]
#define ZV(k,j) zv[((j)-1)*101 + (k)]
#define ZZ(k,j) zz[((j)-1)*101 + (k)]

int main(void) {
    /* 101*7=707, max flat index 707, need [708] */
    double za[708], zb[708], zr[708], zu[708], zv[708], zz[708];

    signel(&za[1], NTOT);
    signel(&zb[1], NTOT);
    signel(&zr[1], NTOT);
    signel(&zu[1], NTOT);
    signel(&zv[1], NTOT);
    signel(&zz[1], NTOT);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long n = 100;
    double fw = 0.175;
    for (long rep = 0; rep < NREPS; rep++) {
        for (long j = 2; j <= 6; j++) {
            for (long k = 2; k <= n; k++) {
                double qa = ZA(k,j+1)*ZR(k,j) + ZA(k,j-1)*ZB(k,j)
                          + ZA(k+1,j)*ZU(k,j) + ZA(k-1,j)*ZV(k,j) + ZZ(k,j);
                ZA(k,j) = ZA(k,j) + fw * (qa - ZA(k,j));
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("za(51,4) = %f\n", ZA(51,4));
    return 0;
}
