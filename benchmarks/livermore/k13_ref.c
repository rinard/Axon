/* K13 — 2-D PIC (Livermore Loop 13) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double p[64][4];
static double b[64][64], c[64][64], h[64][64];
static double y[1001], z[1001];
static long e[96], f[96];

int main(void) {
    int ip, n = 64, rep;
    int i1, j1, i2, j2;

    init_particles((double *)p, 64);
    signel((double *)b, 64 * 64);
    signel((double *)c, 64 * 64);
    for (int i = 0; i < 64; i++)
        for (int j = 0; j < 64; j++)
            h[i][j] = 0.0;
    signel(y, 1001);
    signel(z, 1001);
    for (int i = 0; i < 96; i++) {
        e[i] = i % 64;
        f[i] = i % 64;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* re-init p each rep to avoid drift */
        init_particles((double *)p, 64);
        for (int i = 0; i < 64; i++)
            for (int j = 0; j < 64; j++)
                h[i][j] = 0.0;

        for (ip = 0; ip < n; ip++) {
            i1 = p[ip][0];
            j1 = p[ip][1];
            i1 &= 64-1;
            j1 &= 64-1;
            p[ip][2] += b[j1][i1];
            p[ip][3] += c[j1][i1];
            p[ip][0] += p[ip][2];
            p[ip][1] += p[ip][3];
            i2 = p[ip][0];
            j2 = p[ip][1];
            i2 = (i2 & 64-1) - 1;
            j2 = (j2 & 64-1) - 1;
            p[ip][0] += y[i2+32];
            p[ip][1] += z[j2+32];
            i2 += e[i2+32];
            j2 += f[j2+32];
            h[j2][i2] += 1.0;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K13 2-D PIC: p[0][0] = %.15e\n", p[0][0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
