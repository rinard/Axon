/* K16 — Monte Carlo search loop (Livermore Loop 16) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double plan[300], d[300];
static long zone[300];

int main(void) {
    int n = 75, rep;
    int ii, lb, k2, k3, i1, m, j2, j4, j5, k;
    double tmp;
    double spacer[39]; signel(spacer, 39);
    double r = spacer[29], s = spacer[31], t = spacer[35];

    signel(plan, 300);
    signel(d, 300);
    for (int i = 0; i < 300; i++)
        zone[i] = i % (n + 1);
    zone[0] = 5;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        ii = n/3; lb = ii+ii; k2 = k3 = 0;
        i1 = m = 1;
        label410:
        j2 = (n+n)*(m-1) + 1;
        for (k = 1; k <= n; k++) {
            k2++;
            j4 = j2 + k + k;
            if (j4-1 < 0 || j4-1 >= 300) break;
            j5 = zone[j4-1];
            if (j5 < n) {
                if (j5 < 1) break;
                if (j5+lb < n) tmp = plan[j5-1] - t;
                else if (j5+ii < n) tmp = plan[j5-1] - s;
                else tmp = plan[j5-1] - r;
            } else if (j5 == n) break;
            else {
                if (j5-1 < 0 || j5-1 >= 300 || j5-5 < 0) break;
                k3++;
                tmp=(d[j5-1]-(d[j5-2]*(t-d[j5-3])*(t-d[j5-3])+(s-d[j5-4])*(s-d[j5-4])+(r-d[j5-5])*(r-d[j5-5])));
            }
            if (tmp < 0.0) {
                if (j4-2 < 0 || j4-2 >= 300) break;
                if (zone[j4-2] < 0) continue;
                else if (!zone[j4-2]) break;
            }
            else if (tmp) {
                if (j4-2 < 0 || j4-2 >= 300) break;
                if (zone[j4-2] > 0) continue;
                else if (!zone[j4-2]) break;
            }
            else break;
            m++;
            if (m > zone[0]) m = 1;
            if (i1-m) goto label410;
            else break;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K16 monte carlo: k2 = %d, k3 = %d\n", k2, k3);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
