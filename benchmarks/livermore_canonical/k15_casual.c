/* K15 -- Casual Fortran (canonical, 1-based indexing)
   Canonical body: lines 297-329 of the kernels listing.
   AR=0.053, BR=0.073 hardcoded in canonical pre-loop.
   Column-major: arr(k,j) at flat (j-1)*101 + k. */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

#define NZ    101
#define NG    7
#define NREPS 6600000

#define VY(k,j) vy[((j)-1)*101 + (k)]
#define VH(k,j) vh[((j)-1)*101 + (k)]
#define VF(k,j) vf[((j)-1)*101 + (k)]
#define VG(k,j) vg[((j)-1)*101 + (k)]
#define VS(k,j) vs[((j)-1)*101 + (k)]

#define MAXD(a,b) ((a)>(b)?(a):(b))

int main(void) {
    static double vy[101*7 + 1];
    static double vh[101*7 + 1], vf[101*7 + 1], vg[101*7 + 1], vs[101*7 + 1];

    /* VH */
    double fuzz = 1.2345e-3, buzz = 1.0 + fuzz, fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            VH(i,j) = (buzz - fizz) * 0.1;
        }
    /* VF (must be > 0 -- divisor) */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            VF(i,j) = (buzz - fizz) * 0.1;
            if (VF(i,j) <= 0.0) VF(i,j) = 0.001;
        }
    /* VG */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            VG(i,j) = (buzz - fizz) * 0.1;
        }
    /* VS */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++) {
            buzz = (1.0 - fuzz) * buzz + fuzz;
            fuzz = -fuzz;
            VS(i,j) = (buzz - fizz) * 0.1;
        }
    /* Zero VY */
    for (long j = 1; j <= 7; j++)
        for (long i = 1; i <= 101; i++)
            VY(i,j) = 0.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double ar, br, r, s, t;
    for (long rep = 1; rep <= NREPS; rep++) {
        ar = 0.053; br = 0.073;
        for (long j = 2; j <= NG; j++) {
            for (long k = 2; k <= NZ; k++) {
                /* IF (j - NG) 31, 30, 30 -- neg->31, zero/pos->30 */
                if (j >= NG) {
                    VY(k,j) = 0.0;
                    continue;
                }
                /* label 31: */
                if (VH(k,j+1) > VH(k,j)) t = ar; else t = br;

                if (VF(k,j) < VF(k-1,j)) {
                    r = MAXD(VH(k-1,j), VH(k-1,j+1));
                    s = VF(k-1,j);
                } else {
                    r = MAXD(VH(k,j), VH(k,j+1));
                    s = VF(k,j);
                }
                VY(k,j) = sqrt(VG(k,j)*VG(k,j) + r*r) * t / s;

                /* IF (k - NZ) 40, 39, 39 -- neg->40, zero/pos->39 */
                if (k >= NZ) {
                    VS(k,j) = 0.0;
                    continue;
                }
                /* label 40: */
                if (VF(k,j) < VF(k,j-1)) {
                    r = MAXD(VG(k,j-1), VG(k+1,j-1));
                    s = VF(k,j-1);
                    t = br;
                } else {
                    r = MAXD(VG(k,j), VG(k+1,j));
                    s = VF(k,j);
                    t = ar;
                }
                VS(k,j) = sqrt(VH(k,j)*VH(k,j) + r*r) * t / s;
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vy(2,2) = %.15e\n", VY(2,2));
    return 0;
}
