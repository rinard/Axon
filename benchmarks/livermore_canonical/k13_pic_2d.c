/* K13 -- 2-D Particle in Cell (canonical, 1-based indexing)
   Canonical body: lines 211-231 of the kernels listing.
   MOD2N(i, 64) = i & 63.
   H is over-allocated to 128x128 to fit canonical's i2,j2 range. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     64
#define NREPS 33800000

/* Column-major 1-based: arr(j,k) = arr[(k-1)*Nfast + j] */
#define P(j,k) p[((k)-1)*4 + (j)]
#define B(i,j) b[((j)-1)*64 + (i)]
#define CC(i,j) cc[((j)-1)*64 + (i)]
#define H(i,j) h[((j)-1)*128 + (i)]

int main(void) {
    static double p[4*64 + 1];
    static double b[64*64 + 1], cc[64*64 + 1];
    static double h[128*128 + 1];
    static double y[1002], z[1002];
    static long e[97], f[97];

    /* Init P via DS=1.0, DW=0.5 ramp (j outer, k inner) */
    double ds = 1.0, dw = 0.5;
    for (long j = 1; j <= 4; j++) {
        for (long k = 1; k <= 64; k++) {
            P(j,k) = ds;
            ds += dw;
        }
    }

    /* Init B using SIGNEL */
    double fuzz = 1.2345e-3, buzz = 1.0 + fuzz, fizz = 1.1 * fuzz;
    for (long j = 1; j <= 64; j++)
        for (long i = 1; i <= 64; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            B(i,j) = (buzz - fizz) * 0.1;
        }

    /* Init C using SIGNEL */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 64; j++)
        for (long i = 1; i <= 64; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            CC(i,j) = (buzz - fizz) * 0.1;
        }

    /* Zero H (128x128) */
    for (long j = 1; j <= 128; j++)
        for (long i = 1; i <= 128; i++)
            H(i,j) = 0.0;

    /* Init Y, Z using SIGNEL */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 1001; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        y[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 1001; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        z[k] = (buzz - fizz) * 0.1;
    }

    /* Init E, F (mod-64 pattern) */
    for (long i = 1; i <= 96; i++) {
        e[i] = (i - 1) % 64;
        f[i] = (i - 1) % 64;
    }

    double fw = 1.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 1; rep <= NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            long i1 = (long)P(1,k);
            long j1 = (long)P(2,k);
            i1 = 1 + (i1 & 63);
            j1 = 1 + (j1 & 63);
            P(3,k) = P(3,k) + B(i1,j1);
            P(4,k) = P(4,k) + CC(i1,j1);
            P(1,k) = P(1,k) + P(3,k);
            P(2,k) = P(2,k) + P(4,k);
            long i2 = (long)P(1,k);
            long j2 = (long)P(2,k);
            i2 = i2 & 63;
            j2 = j2 & 63;
            P(1,k) = P(1,k) + y[i2+32];
            P(2,k) = P(2,k) + z[j2+32];
            i2 = i2 + e[i2+32];
            j2 = j2 + f[j2+32];
            H(i2,j2) = H(i2,j2) + fw;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("p(1,1) = %.15e\n", P(1,1));
    return 0;
}
