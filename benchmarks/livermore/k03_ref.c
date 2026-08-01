/* K3 — Inner product (Livermore Loop 3) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double z[1001], x[1001];

int main(void) {
    int k, n = 1001, rep;
    double q;

    signel(z, 1001);
    signel(x, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        q = 0.0;
        for (k = 0; k < n; k++) {
            q += z[k] * x[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K3 inner product: q = %.15e\n", q);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
