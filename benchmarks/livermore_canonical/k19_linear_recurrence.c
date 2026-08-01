/* K19 -- General Linear Recurrence Equations (canonical, 1-based indexing)
   Canonical body (forward + backward sweep, both executed):
     KB5I = 0
     DO 191 k=1,n: B5(k+KB5I) = SA(k) + STB5*SB(k); STB5 = B5(k+KB5I) - STB5
     DO 193 i=1,n: k=n-i+1; B5(k+KB5I) = SA(k) + STB5*SB(k); STB5 = B5(k+KB5I) - STB5 */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 39200000

int main(void) {
    double b5[102], sa[102], sb[102];
    double spacer[40];

    signel(spacer+1, 39);
    double stb5_init = spacer[35];

    signel(sa+1, 101);
    signel(sb+1, 101);
    for (long k = 1; k <= 101; k++) b5[k] = 0.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long kb5i;
    double stb5;
    for (long rep = 0; rep < NREPS; rep++) {
        stb5 = stb5_init;
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
    printf("b5[n] = %f\n", b5[N]);
    return 0;
}
