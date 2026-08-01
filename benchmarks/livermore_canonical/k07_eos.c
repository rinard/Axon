/* K7 -- Equation of state fragment (canonical, 1-based indexing)
   Canonical body:
     X(k) = U(k) + R*(Z(k) + R*Y(k))
          + T*(U(k+3) + R*(U(k+2) + R*U(k+1))
          + T*(U(k+6) + Q*(U(k+5) + Q*U(k+4)))) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     995
#define NREPS 17000000

int main(void) {
    /* U needs k+6 access; allocate [1002] but only fill 1..1001 */
    double x[1002], u[1002], z[1002], y[1002];
    double spacer[40];

    signel(spacer+1, 39);
    double q = spacer[28], r = spacer[30], t = spacer[36];

    signel(u+1, 1001);
    signel(z+1, 1001);
    signel(y+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            x[k] = u[k] + r*(z[k] + r*y[k])
                 + t*(u[k+3] + r*(u[k+2] + r*u[k+1])
                 + t*(u[k+6] + q*(u[k+5] + q*u[k+4])));
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[1] = %f\n", x[1]);
    return 0;
}
