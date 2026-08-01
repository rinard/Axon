/* K20 — Discrete ordinates transport (Livermore Loop 20) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double x[1001], y[1001], z[1001], w[1001], v[1001];
static double u[1001], g[1001], xx[1001], vx[1001];

int main(void) {
    int k, n = 1000, rep;
    double di, dn;
    double spacer[39]; signel(spacer, 39);
    double dk = spacer[14], s = spacer[31], t = spacer[35];

    signel(x, 1001);
    signel(y, 1001);
    signel(z, 1001);
    signel(w, 1001);
    signel(v, 1001);
    signel(u, 1001);
    signel(g, 1001);
    signel(xx, 1001);
    signel(vx, 1001);
    /* Ensure xx[k]+dk and vx[k]+v[k]*dn are nonzero */
    for (int i = 0; i < 1001; i++) {
        xx[i] += 1.0;
        vx[i] += 2.0;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* re-init xx to avoid drift */
        signel(xx, 1001);
        for (int i = 0; i < 1001; i++) xx[i] += 1.0;

        for (k = 0; k < n; k++) {
            di = y[k] - g[k]/(xx[k] + dk);
            dn = 0.2;
            if (di) {
                dn = z[k]/di;
                if (t < dn) dn = t;
                if (s > dn) dn = s;
            }
            x[k] = ((w[k] + v[k]*dn)*xx[k] + u[k])/(vx[k] + v[k]*dn);
            xx[k+1] = (x[k] - xx[k])*dn + xx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K20 discrete ord: x[0] = %.15e\n", x[0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
