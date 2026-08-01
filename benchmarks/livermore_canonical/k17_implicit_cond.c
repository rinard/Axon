/* K17 -- Implicit conditional computation (canonical, 1-based indexing)
   Canonical body: lines 394-427 of the kernels listing.
   dw, fw, tw set locally in the kernel (no spacer). */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 66400000

int main(void) {
    static double vsp[102], vstp[102], vxne[102], vxnd[102];
    static double ve3[102], vlr[102], vlin[102];

    double fuzz, buzz, fizz;

    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 101; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
        vsp[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 101; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
        vstp[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 101; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
        vxne[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 101; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
        vxnd[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 101; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
        ve3[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 101; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
        vlr[k] = (buzz - fizz) * 0.1;
    }
    fuzz = 1.2345e-3; buzz = 1.0 + fuzz; fizz = 1.1 * fuzz;
    for (long k = 1; k <= 101; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz; fuzz = -fuzz;
        vlin[k] = (buzz - fizz) * 0.1;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long k_var, j, ink;
    double scale, xnm, e3, e6, xnei, xnc;
    double dw, fw, tw;

    for (long rep = 1; rep <= NREPS; rep++) {
        dw = 5.0 / 3.0;
        fw = 1.0 / 3.0;
        tw = 1.03 / 3.07;
        k_var = N;
        j = 1;
        ink = -1;
        scale = dw;
        xnm   = fw;
        e6    = tw;
        goto L61;
    L60:
        e6 = xnm * vsp[k_var] + vstp[k_var];
        vxne[k_var] = e6;
        xnm = e6;
        ve3[k_var] = e6;
        k_var = k_var + ink;
        if (k_var == j) goto L62;
    L61:
        e3 = xnm * vlr[k_var] + vlin[k_var];
        xnei = vxne[k_var];
        vxnd[k_var] = e6;
        xnc = scale * e3;
        if (xnm  > xnc) goto L60;
        if (xnei > xnc) goto L60;
        ve3[k_var] = e3;
        e6 = e3 + e3 - xnm;
        vxne[k_var] = e3 + e3 - xnei;
        xnm = e6;
        k_var = k_var + ink;
        if (k_var != j) goto L61;
    L62: ;
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vxne(n) = %.15e\n", vxne[N]);
    return 0;
}
