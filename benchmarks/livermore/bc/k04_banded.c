/* K4 — Banded linear equations (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION X(1201), Y(1001), N=1001, M=(1001-7)/2
   DO K=7,1001,M: LW=K-6; DO J=5,N,5: TEMP=TEMP-X(LW)*Y(J); LW=LW+1
   X(K)=Y(5)*TEMP */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 10000

int main(void) {
    double x[1202], y[1002];

    signel(x+1, 1001);
    signel(y+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        signel(x+1, 1001);
        long m = (N - 7) / 2;
        for (long k = 7; k <= N; k = k + m) {
            long lw = k - 6;
            double temp = x[k];
            for (long j = 5; j <= N; j = j + 5) {
                temp = temp - x[lw] * y[j];
                if (lw >= 1202 || j >= 1002) { 
                  printf("%ld < 1202 %ld < 1002\n", lw, j);
                }
                lw = lw + 1;
            }
            x[k] = y[5] * temp;
            if (k >= 1202) {
              printf("%ld < 1202\n", k);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[7] = %f\n", x[7]);
    return 0;
}
