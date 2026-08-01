/* K6 — General linear recurrence (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION W(1001), B(64,64), N=64
   DO I=2,N: DO K=1,I-1: W(I) = W(I) + B(K,I)*W(I-K)
   B is column-major: B(K,I) at flat offset (I-1)*64 + K (1-based) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NW    64
#define NREPS 2781000

int main(void) {
    double w[1002];
    /* b is 1-based: b[(i-1)*64 + k] for k=1..64, i=1..64, range 1..4096 */
    double b[4097];

    signel(b+1, NW * NW);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long j = 1; j <= 1001; j++) w[j] = 0.0;
        w[1] = 0.01;
        for (long i = 2; i <= NW; i++) {
            for (long k = 1; k <= i-1; k++) {
                w[i] = w[i] + b[(i-1)*64 + k] * w[i-k];
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("w[64] = %f\n", w[64]);
    return 0;
}
