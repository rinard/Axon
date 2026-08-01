/* K18 — 2-D Explicit Hydrodynamics (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION ZA(101,7), ZP(101,7), ZQ(101,7), ZR(101,7),
            ZM(101,7), ZB(101,7), ZU(101,7), ZV(101,7), ZZ(101,7)
   KN=6, JN=100. Column-major: arr(J,K) at flat (K-1)*101 + J (1-based) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define JN  100
#define KN  6
#define JD  101
#define KD  7
#define NREPS 1382000

/* 1-based column-major: arr(j,k) with first dim 101 */
#define ZA(j,k) za[((k)-1)*101 + (j)]
#define ZP(j,k) zp[((k)-1)*101 + (j)]
#define ZQ(j,k) zq[((k)-1)*101 + (j)]
#define ZR(j,k) zr[((k)-1)*101 + (j)]
#define ZM(j,k) zm[((k)-1)*101 + (j)]
#define ZB(j,k) zb[((k)-1)*101 + (j)]
#define ZU(j,k) zu[((k)-1)*101 + (j)]
#define ZV(j,k) zv[((k)-1)*101 + (j)]
#define ZZ(j,k) zz[((k)-1)*101 + (j)]

int main(void) {
    /* 101*7=707, max flat index 707, need [708] */
    double za[708], zp[708], zq[708], zr[708];
    double zm[708], zb[708], zu[708], zv[708], zz[708];

    /* Initialise arrays (1-based) */
    signel(&zp[1], JD * KD);
    signel(&zq[1], JD * KD);
    signel(&zr[1], JD * KD);
    signel(&zm[1], JD * KD);
    /* Ensure zm large enough for division */
    for (long i = 1; i <= JD * KD; i++) zm[i] += 10.0;
    signel(&zz[1], JD * KD);
    /* Zero out za, zb, zu, zv */
    for (long k = 1; k <= KD; k++)
        for (long j = 1; j <= JD; j++) {
            ZA(j,k) = 0.0; ZB(j,k) = 0.0;
            ZU(j,k) = 0.0; ZV(j,k) = 0.0;
        }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double t, s;
    for (long l = 0; l < NREPS; l++) {
        t = 0.0037; s = 0.0041;

        /* Phase 1: compute ZA, ZB */
        for (long k = 2; k <= KN; k++)
            for (long j = 2; j <= JN; j++) {
                ZA(j,k) = (ZP(j-1,k+1)+ZQ(j-1,k+1)-ZP(j-1,k)-ZQ(j-1,k))
                          *(ZR(j,k)+ZR(j-1,k))
                          /(ZM(j-1,k)+ZM(j-1,k+1));
                ZB(j,k) = (ZP(j-1,k)+ZQ(j-1,k)-ZP(j,k)-ZQ(j,k))
                          *(ZR(j,k)+ZR(j,k-1))
                          /(ZM(j,k)+ZM(j-1,k));
            }

        /* Phase 2: update ZU, ZV */
        for (long k = 2; k <= KN; k++)
            for (long j = 2; j <= JN; j++) {
                ZU(j,k) = ZU(j,k)
                  + s*(ZA(j,k)*(ZZ(j,k)-ZZ(j+1,k))
                      -ZA(j-1,k)*(ZZ(j,k)-ZZ(j-1,k))
                      -ZB(j,k)*(ZZ(j,k)-ZZ(j,k-1))
                      +ZB(j,k+1)*(ZZ(j,k)-ZZ(j,k+1)));
                ZV(j,k) = ZV(j,k)
                  + s*(ZA(j,k)*(ZR(j,k)-ZR(j+1,k))
                      -ZA(j-1,k)*(ZR(j,k)-ZR(j-1,k))
                      -ZB(j,k)*(ZR(j,k)-ZR(j,k-1))
                      +ZB(j,k+1)*(ZR(j,k)-ZR(j,k+1)));
            }

        /* Phase 3: update ZR, ZZ */
        for (long k = 2; k <= KN; k++)
            for (long j = 2; j <= JN; j++) {
                ZR(j,k) = ZR(j,k) + t*ZU(j,k);
                ZZ(j,k) = ZZ(j,k) + t*ZV(j,k);
            }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("zu(51,4) = %f\n", ZU(51,4));
    return 0;
}
