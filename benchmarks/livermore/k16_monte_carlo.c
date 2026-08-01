/* K16 — Monte Carlo search (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION D(300), PLAN(300), ZONE(300) (ZONE is INTEGER)
   N=75, II=N/3, LB=II+II */
#include <stdio.h>
#include <time.h>
#include <stdint.h>
#include "signel.h"

#define N     75
#define NREPS 162000000

int main(void) {
    double d[301], plan[301];
    long zone[301];

    /* Initialize arrays (1-based) */
    signel(d+1, 300);
    signel(plan+1, 300);
    for (long i = 1; i <= 300; i++)
        zone[i] = (i - 1) % (N + 1);
    zone[1] = 5;

    double r = 0.05, s = 0.05, t = 0.05;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long k2, k3, m, i1, j2, j4, j5;
    long ii, lb;
    double tmp;
    for (long rep = 0; rep < NREPS; rep++) {
        ii = N / 3; lb = ii + ii;
        i1 = 1; m = 1; k2 = 0; k3 = 0;
label410:
        j2 = (N + N) * (m - 1) + 1;
        for (long k = 1; k <= N; k++) {
            k2 = k2 + 1;
            j4 = j2 + k + k;
            if (j4-1 < 1 || j4-1 > 300) break;
            j5 = zone[j4-1];
            if (j5 < N) {
                if (j5 < 1) break;
                if (j5 + lb < N) tmp = plan[j5] - t;
                else if (j5 + ii < N) tmp = plan[j5] - s;
                else tmp = plan[j5] - r;
            } else if (j5 == N) {
                break;  /* GO TO 480 */
            } else {
                if (j5-1 < 1 || j5-5 < 1) break;
                k3 = k3 + 1;
                tmp = d[j5-1] - (d[j5-2]*(t-d[j5-3])*(t-d[j5-3])
                      + (s-d[j5-4])*(s-d[j5-4])
                      + (r-d[j5-5])*(r-d[j5-5]));
            }

            if (tmp < 0.0) {
                if (j4-2 < 1 || j4-2 > 300) break;
                if (zone[j4-2] < 0) continue;   /* GO TO 470 */
                if (zone[j4-2] == 0) break;      /* GO TO 480 */
            } else if (tmp > 0.0) {
                if (j4-2 < 1 || j4-2 > 300) break;
                if (zone[j4-2] > 0) continue;   /* GO TO 470 */
                if (zone[j4-2] == 0) break;      /* GO TO 480 */
            } else {
                break;  /* GO TO 480 */
            }

            m = m + 1;
            if (m > zone[1]) m = 1;
            if (i1 != m) goto label410;
            else break;  /* i1 == m -> GO TO 480 */
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("k2 = %ld, k3 = %ld\n", k2, k3);
    return 0;
}
