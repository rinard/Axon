/* K18 -- 2-D explicit hydrodynamics fragment (canonical, 1-based indexing)
   Canonical body: lines 438-466 of the kernels listing.
   T=0.0037, S=0.0041 hardcoded in canonical pre-loop.
   JN set to n-1 (=100) so j+1 access stays within 101-wide fast dim.
   ZM gets +10 offset to keep divisor bounded away from 0.
   Column-major: arr(j,k) at flat (k-1)*101 + j. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 3840000

#define ZA(j,k) za[((k)-1)*101 + (j)]
#define ZB(j,k) zb[((k)-1)*101 + (j)]
#define ZP(j,k) zp[((k)-1)*101 + (j)]
#define ZQ(j,k) zq[((k)-1)*101 + (j)]
#define ZR(j,k) zr[((k)-1)*101 + (j)]
#define ZM(j,k) zm[((k)-1)*101 + (j)]
#define ZU(j,k) zu[((k)-1)*101 + (j)]
#define ZV(j,k) zv[((k)-1)*101 + (j)]
#define ZZ(j,k) zz[((k)-1)*101 + (j)]

int main(void) {
    static double za[101*7 + 1], zb[101*7 + 1], zp[101*7 + 1], zq[101*7 + 1];
    static double zr[101*7 + 1], zm[101*7 + 1], zu[101*7 + 1], zv[101*7 + 1];
    static double zz[101*7 + 1];

    double fuzz, buzz, fizz;
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
            ZP(i,j) = (buzz - fizz) * 0.1;
        }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
            ZQ(i,j) = (buzz - fizz) * 0.1;
        }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
            ZR(i,j) = (buzz - fizz) * 0.1;
        }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
            ZM(i,j) = (buzz - fizz) * 0.1 + 10.0;
        }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
            ZZ(i,j) = (buzz - fizz) * 0.1;
        }

    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            ZA(i,j) = 0.0;
            ZB(i,j) = 0.0;
            ZU(i,j) = 0.0;
            ZV(i,j) = 0.0;
        }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double t, s;
    long kn, jn;
    for (long rep = 1; rep <= NREPS; rep++) {
        t = 0.0037; s = 0.0041;
        kn = 6; jn = N - 1;
        for (long k = 2; k <= kn; k++)
            for (long j = 2; j <= jn; j++) {
                ZA(j,k) = (ZP(j-1,k+1) + ZQ(j-1,k+1)
                           - ZP(j-1,k) - ZQ(j-1,k))
                         * (ZR(j,k) + ZR(j-1,k))
                         / (ZM(j-1,k) + ZM(j-1,k+1));
                ZB(j,k) = (ZP(j-1,k) + ZQ(j-1,k)
                           - ZP(j,k) - ZQ(j,k))
                         * (ZR(j,k) + ZR(j,k-1))
                         / (ZM(j,k) + ZM(j-1,k));
            }
        for (long k = 2; k <= kn; k++)
            for (long j = 2; j <= jn; j++) {
                ZU(j,k) = ZU(j,k) + s*(ZA(j,k)*(ZZ(j,k)-ZZ(j+1,k))
                                      -ZA(j-1,k)*(ZZ(j,k)-ZZ(j-1,k))
                                      -ZB(j,k)*(ZZ(j,k)-ZZ(j,k-1))
                                      +ZB(j,k+1)*(ZZ(j,k)-ZZ(j,k+1)));
                ZV(j,k) = ZV(j,k) + s*(ZA(j,k)*(ZR(j,k)-ZR(j+1,k))
                                      -ZA(j-1,k)*(ZR(j,k)-ZR(j-1,k))
                                      -ZB(j,k)*(ZR(j,k)-ZR(j,k-1))
                                      +ZB(j,k+1)*(ZR(j,k)-ZR(j,k+1)));
            }
        for (long k = 2; k <= kn; k++)
            for (long j = 2; j <= jn; j++) {
                ZR(j,k) = ZR(j,k) + t*ZU(j,k);
                ZZ(j,k) = ZZ(j,k) + t*ZV(j,k);
            }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("zu(51,4) = %.15e\n", ZU(51,4));
    return 0;
}
