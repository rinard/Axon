/* K16 -- Monte Carlo search loop (canonical, 1-based indexing)
   Canonical body: lines 351-385 of the kernels listing.
   R, S, T from canonical SPACER positions 30, 32, 36. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     75
#define NREPS 400000000

int main(void) {
    static double d[301], plan[301];
    static long zone[301];
    static double spacer[40];

    /* SPACER -> R, S, T */
    double fuzz = 1.2345e-3, buzz = 1.0 + fuzz, fizz = 1.1 * fuzz;
    for (long k = 1; k <= 39; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        spacer[k] = (buzz - fizz) * 0.1;
    }
    double r = spacer[30], s = spacer[32], t = spacer[36];

    /* PLAN, D via SIGNEL (independent streams) */
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long i = 1; i <= 300; i++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        plan[i] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long i = 1; i <= 300; i++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        d[i] = (buzz - fizz) * 0.1;
    }

    /* ZONE */
    long ii = N / 3, lb = ii + ii;
    for (long i = 1; i <= 300; i++)
        zone[i] = (i - 1) % (N + 1);
    zone[1] = 5;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long k2 = 0, k3 = 0;
    long m, i1, j2, j4, j5;
    double tmp, dexpr;

    for (long rep = 1; rep <= NREPS; rep++) {
        m = 1;
        i1 = m;
        k2 = 0;
        k3 = 0;
    L410:
        j2 = (N + N) * (m - 1) + 1;
        for (long k = 1; k <= N; k++) {
            k2 = k2 + 1;
            j4 = j2 + k + k;
            j5 = zone[j4];
            if (j5 < N) goto L420;
            if (j5 == N) goto L475;
            goto L450;
        L415:
            if (j5 < N - ii) goto L430;
            goto L425;
        L420:
            if (j5 < N - lb) goto L435;
            goto L415;
        L425:
            tmp = plan[j5] - r;
            goto L446;
        L430:
            tmp = plan[j5] - s;
            goto L446;
        L435:
            tmp = plan[j5] - t;
            goto L446;
        L440:
            if (zone[j4-1] < 0) goto L455;
            if (zone[j4-1] == 0) goto L485;
            continue;  /* GO TO 470 */
        L445:
            if (zone[j4-1] < 0) continue;  /* GO TO 470 */
            if (zone[j4-1] == 0) goto L485;
            goto L455;
        L446:
            if (tmp < 0.0) goto L445;
            if (tmp == 0.0) goto L480;
            goto L440;
        L450:
            k3 = k3 + 1;
            dexpr = d[j5] - (d[j5-1]*(t-d[j5-2])*(t-d[j5-2])
                             + (s-d[j5-3])*(s-d[j5-3])
                             + (r-d[j5-4])*(r-d[j5-4]));
            if (dexpr < 0.0) goto L445;
            if (dexpr == 0.0) goto L480;
            goto L440;
        L455:
            m = m + 1;
            if (m > zone[1]) m = 1;
            if (i1 == m) goto L480;
            goto L410;
        }
    L475: ;
    L480: ;
    L485: ;
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("k2 = %ld\n", k2);
    printf("k3 = %ld\n", k3);
    return 0;
}
