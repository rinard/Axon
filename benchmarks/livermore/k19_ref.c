/* K19 — General linear recurrence equations (Livermore Loop 19) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double b5[101], sa[101], sb[101];

int main(void) {
    int n = 101, rep;
    int i, k, kb5i;
    double stb5;

    signel(sa, 101);
    signel(sb, 101);
    for (int ii = 0; ii < 101; ii++) b5[ii] = 0.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        stb5 = 0.5;
        kb5i = 0;
        for (k = 0; k < n; k++) {
            b5[k+kb5i] = sa[k] + stb5*sb[k];
            stb5 = b5[k+kb5i] - stb5;
        }
        for (i = 1; i <= n; i++) {
            k = n - i;
            b5[k+kb5i] = sa[k] + stb5*sb[k];
            stb5 = b5[k+kb5i] - stb5;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K19 linear recurrence: b5[50] = %.15e\n", b5[50]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
