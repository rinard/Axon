/* K17 — Implicit conditional computation (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION VSP(101), VSTP(101), VXNE(101), VXND(101),
            VE3(101), VLR(101), VLIN(101)
   N=101, I=N-1, INK=-1, J=0. Accesses arr(I+1). */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 23048000

int main(void) {
    static double vsp[102], vstp[102], vxne[102], vxnd[102];
    static double ve3[102], vlr[102], vlin[102];

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long i, j, ink;
    double scale, xnm, e6, e3, xnei, xnc;

    for (long rep = 0; rep < NREPS; rep++) {
        signel(vsp+1, N); signel(vstp+1, N); signel(vxne+1, N); signel(vxnd+1, N);
        signel(ve3+1, N); signel(vlr+1, N); signel(vlin+1, N);

        i = N - 1; j = 0; ink = -1;
        scale = 5.0 / 3.0; xnm = 1.0 / 3.0; e6 = 1.03 / 3.07;
        goto l61;
    l60:
        e6 = xnm * vsp[i+1] + vstp[i+1];
        vxne[i+1] = e6;
        xnm = e6;
        ve3[i+1] = e6;
        i = i + ink;
        if (i == j) goto l62;
    l61:
        e3 = xnm * vlr[i+1] + vlin[i+1];
        xnei = vxne[i+1];
        vxnd[i+1] = e6;
        xnc = scale * e3;
        if (xnm > xnc) goto l60;
        if (xnei > xnc) goto l60;
        ve3[i+1] = e3;
        e6 = e3 + e3 - xnm;
        vxne[i+1] = e3 + e3 - xnei;
        xnm = e6;
        i = i + ink;
        if (i != j) goto l61;
    l62: ;
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("ve3[51] = %f\n", ve3[51]);
    return 0;
}
