/* K23 — 2-D Implicit Hydrodynamics (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION ZA(101,7), ZR(101,7), ZB(101,7),
            ZU(101,7), ZV(101,7), ZZ(101,7)
   N=100. DO J=2,6: DO K=2,N:
     QA = ZA(K,J+1)*ZR(K,J) + ZA(K,J-1)*ZB(K,J)
        + ZA(K+1,J)*ZU(K,J) + ZA(K-1,J)*ZV(K,J) + ZZ(K,J)
     ZA(K,J) = ZA(K,J) + 0.175*(QA - ZA(K,J))
   Column-major: arr(K,J) at flat (J-1)*101 + K (1-based) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define JD    101
#define KD    7
#define NTOT  (JD * KD)
#define NREPS 8581000

/* 1-based column-major: arr(k,j) with first dim 101 */
#define ZA(k,j) za[((j)-1)*101 + (k)]
#define ZR(k,j) zr[((j)-1)*101 + (k)]
#define ZB(k,j) zb[((j)-1)*101 + (k)]
#define ZU(k,j) zu[((j)-1)*101 + (k)]
#define ZV(k,j) zv[((j)-1)*101 + (k)]
#define ZZ(k,j) zz[((j)-1)*101 + (k)]

int main(void) {
    /* 101*7=707, max flat index 707, need [708] */
    double za[708], zr[708], zb[708], zu[708], zv[708], zz[708];

    signel(&za[1], NTOT);
    signel(&zr[1], NTOT);
    signel(&zb[1], NTOT);
    signel(&zu[1], NTOT);
    signel(&zv[1], NTOT);
    signel(&zz[1], NTOT);
    /* Scale coefficients for stable relaxation */
    for (long i = 1; i <= NTOT; i++) {
        zr[i] *= 0.1; zb[i] *= 0.1; zu[i] *= 0.1; zv[i] *= 0.1;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long n = 100;
    for (long rep = 0; rep < NREPS; rep++) {
        for (long j = 2; j <= 6; j++) {
            for (long k = 2; k <= n; k++) {
                double qa = ZA(k,j+1)*ZR(k,j) + ZA(k,j-1)*ZB(k,j)
                          + ZA(k+1,j)*ZU(k,j) + ZA(k-1,j)*ZV(k,j) + ZZ(k,j);
                ZA(k,j) = ZA(k,j) + 0.175 * (qa - ZA(k,j));
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("za(51,4) = %f\n", ZA(51,4));
    return 0;
}
