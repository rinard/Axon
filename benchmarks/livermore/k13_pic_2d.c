#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NPART 64
#define NGRID 64
#define NREPS 2570000

/* P(K,J) 1-based, column-major (64,4) */
#define P(k,j) p[((j)-1)*64 + (k)]
/* B(I,J), C(I,J), H(I,J) 1-based, column-major (64,64) */
#define B(i,j) b[((j)-1)*64 + (i)]
#define CC(i,j) cc[((j)-1)*64 + (i)]
#define H(i,j) h[((j)-1)*64 + (i)]

int main(void) {
    double p[257], b[4097], cc[4097], h[6177];
    double y[1002], z[1002];
    long e[97], f[97];

    /* Init P */
    double ds = 1.0, dw = 0.5;
    for (long j = 1; j <= 4; j++)
        for (long k = 1; k <= 64; k++) {
            P(k,j) = ds;
            ds += dw;
        }

    /* Init B using signel pattern */
    double fuzz = 1.2345e-3, buzz = 1.0 + fuzz, fizz = 1.1 * fuzz;
    for (long j = 1; j <= 64; j++)
        for (long i = 1; i <= 64; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            B(i,j) = (buzz - fizz) * 0.1;
        }

    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 64; j++)
        for (long i = 1; i <= 64; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            CC(i,j) = (buzz - fizz) * 0.1;
        }

    for (long j = 1; j <= 64; j++)
        for (long i = 1; i <= 64; i++)
            H(i,j) = 0.0;

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

    for (long i = 1; i <= 96; i++) {
        e[i] = (i-1) % 64;
        f[i] = (i-1) % 64;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 1; rep <= NREPS; rep++) {
        ds = 1.0; dw = 0.5;
        for (long j = 1; j <= 4; j++)
            for (long k = 1; k <= 64; k++) {
                P(k,j) = ds;
                ds += dw;
            }
        for (long j = 1; j <= 64; j++)
            for (long i = 1; i <= 64; i++)
                H(i,j) = 0.0;

        for (long ip = 1; ip <= NPART; ip++) {
            long i1 = (long)P(ip,1);
            long j1 = (long)P(ip,2);
            i1 = i1 & 63;
            j1 = j1 & 63;
            P(ip,3) = P(ip,3) + B(i1+1,j1+1);
            P(ip,4) = P(ip,4) + CC(i1+1,j1+1);
            P(ip,1) = P(ip,1) + P(ip,3);
            P(ip,2) = P(ip,2) + P(ip,4);
            long i2 = (long)P(ip,1);
            long j2 = (long)P(ip,2);
            i2 = (i2 & 63) - 1;
            j2 = (j2 & 63) - 1;
            P(ip,1) = P(ip,1) + y[i2+32];
            P(ip,2) = P(ip,2) + z[j2+32];
            i2 = i2 + e[i2+32];
            j2 = j2 + f[j2+32];
            H(i2+1,j2+1) = H(i2+1,j2+1) + 1.0;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("p(1,1) = %.15e\n", P(1,1));
    return 0;
}
