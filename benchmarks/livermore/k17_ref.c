/* K17 — Implicit, conditional computation (Livermore Loop 17) — netlib reference */
#include <stdio.h>
#include <time.h>
#include "signel.h"

static double vsp[101], vstp[101], vxne[101], vxnd[101];
static double ve3[101], vlr[101], vlin[101];

int main(void) {
    int n = 101, rep;
    int i, j, ink;
    double scale, xnm, e6, e3, xnei, xnc;

    signel(vsp, 101);
    signel(vstp, 101);
    signel(vxne, 101);
    signel(vxnd, 101);
    signel(ve3, 101);
    signel(vlr, 101);
    signel(vlin, 101);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* re-init to avoid accumulation */
        signel(vsp, 101);
        signel(vstp, 101);
        signel(vxne, 101);
        signel(vxnd, 101);
        signel(ve3, 101);
        signel(vlr, 101);
        signel(vlin, 101);

        i = n-1; j = 0; ink = -1;
        scale = 5.0/3.0; xnm = 1.0/3.0; e6 = 1.03/3.07;
        goto l61;
        l60: e6 = xnm*vsp[i] + vstp[i];
             vxne[i] = e6; xnm = e6; ve3[i] = e6;
             i += ink;
             if (i==j) goto l62;
        l61: e3 = xnm*vlr[i] + vlin[i];
             xnei = vxne[i]; vxnd[i] = e6;
             xnc = scale*e3;
             if (xnm > xnc) goto l60;
             if (xnei > xnc) goto l60;
             ve3[i] = e3;
             e6 = e3 + e3 - xnm;
             vxne[i] = e3 + e3 - xnei;
             xnm = e6;
             i += ink;
             if (i != j) goto l61;
        l62: ;
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K17 implicit cond: ve3[50] = %.15e\n", ve3[50]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}
