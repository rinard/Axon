/* K6 -- General linear recurrence equations (canonical, 1-based indexing)
   Canonical body: DO i=2,n: W(i)=0.01; DO k=1,i-1: W(i)=W(i)+B(i,k)*W(i-k)
   B is column-major (i fast, k slow); flat 1-based index = (k-1)*64 + i. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NW    64
#define NREPS 10000000

int main(void) {
    double w[65];
    /* b is 1-based; column-major (i fast, k slow): b[(k-1)*64 + i], i,k=1..64 */
    double b[64*64 + 1];

    signel(b+1, NW * NW);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long j = 1; j <= NW; j++) w[j] = 0.0;
        w[1] = 0.01;
        for (long i = 2; i <= NW; i++) {
            w[i] = 0.01;
            for (long k = 1; k <= i-1; k++) {
                w[i] = w[i] + b[(k-1)*64 + i] * w[i-k];
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("w[64] = %f\n", w[64]);
    return 0;
}
