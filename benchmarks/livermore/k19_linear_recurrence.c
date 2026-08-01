/* K19 — General Linear Recurrence Equations (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION B5(1001), SA(1001), SB(1001), N=101
   Forward: DO K=1,N: B5(K+KB5I) = SA(K) + STB5*SB(K); STB5 = B5(K+KB5I) - STB5
   Backward: DO I=1,N: K=N-I+1; same recurrence */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 30088000

int main(void) {
    double b5[1002], sa[1002], sb[1002];

    signel(sa+1, 101);
    signel(sb+1, 101);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long kb5i;
    for (long rep = 0; rep < NREPS; rep++) {
        double stb5 = 0.5;
        kb5i = 0;
        /* Forward sweep */
        for (long k = 1; k <= N; k++) {
            b5[k+kb5i] = sa[k] + stb5 * sb[k];
            stb5 = b5[k+kb5i] - stb5;
        }
        /* Backward sweep */
        for (long i = 1; i <= N; i++) {
            long k = N - i + 1;
            b5[k+kb5i] = sa[k] + stb5 * sb[k];
            stb5 = b5[k+kb5i] - stb5;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("b5[51] = %f\n", b5[51]);
    return 0;
}
