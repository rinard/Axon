/* K20 -- Discrete Ordinates Transport (canonical, 1-based indexing)
   Canonical body:
     dw = 0.2
     DO 20 k=1,n:
       DI = Y(k) - G(k)/(XX(k)+DK)
       DN = dw
       IF (DI .NE. 0.0) DN = MAX(S, MIN(Z(k)/DI, T))
       X(k) = ((W(k)+V(k)*DN)*XX(k) + U(k))/(VX(k)+V(k)*DN)
       XX(k+1) = (X(k)-XX(k))*DN + XX(k) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1000
#define NREPS 2260000

int main(void) {
    double x[1002], y[1002], z[1002], u[1002], v[1002], w[1002];
    double g[1002], xx[1002], vx[1002];
    double spacer[40];

    signel(spacer+1, 39);
    double dk = spacer[15], s = spacer[32], t = spacer[36];

    signel(x+1, 1001);
    signel(y+1, 1001);
    signel(z+1, 1001);
    signel(u+1, 1001);
    signel(v+1, 1001);
    signel(w+1, 1001);
    signel(g+1, 1001);
    signel(xx+1, 1001);
    signel(vx+1, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double dw = 0.2;
    for (long rep = 0; rep < NREPS; rep++) {
        for (long k = 1; k <= N; k++) {
            double di = y[k] - g[k] / (xx[k] + dk);
            double dn = dw;
            if (di != 0.0) {
                double tmp = z[k] / di;
                if (t < tmp) tmp = t;
                if (s > tmp) tmp = s;
                dn = tmp;
            }
            x[k] = ((w[k] + v[k]*dn)*xx[k] + u[k]) / (vx[k] + v[k]*dn);
            xx[k+1] = (x[k] - xx[k])*dn + xx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[n] = %f\n", x[N]);
    return 0;
}
