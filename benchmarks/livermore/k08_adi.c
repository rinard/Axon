/* K8 — ADI Integration (1-based indexing, matches Fortran exactly)
   Fortran: DIMENSION U1(2,101,5), U2(2,101,5), U3(2,101,5)
            DIMENSION DU1(101), DU2(101), DU3(101)
   N=100, NL1=1, NL2=2, KX=2..3, KY=2..N-1
   Fortran column-major: U1(K1,K2,K3) at (K3-1)*2*101 + (K2-1)*2 + K1
   (1-based flat index) */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NDIM  101
#define N     100
#define KXD   5
#define NREPS 10535000

/* 1-based Fortran column-major access for U(k1,k2,k3) with dims (2,101,5) */
#define U(arr,k1,k2,k3) arr[((k3)-1)*202 + ((k2)-1)*2 + (k1)]

int main(void) {
    /* Max flat index: (5-1)*202 + (101-1)*2 + 2 = 1010, need [1011] */
    double u1[1011], u2[1011], u3[1011];
    double du1[102], du2[102], du3[102];
    double spacer[40]; signel(spacer+1, 39);
    double a11 = spacer[1], a12 = spacer[2], a13 = spacer[3];
    double a21 = spacer[4], a22 = spacer[5], a23 = spacer[6];
    double a31 = spacer[7], a32 = spacer[8], a33 = spacer[9];
    double sig = spacer[34];

    /* Initialise: fill 1010 elements starting at index 1 */
    signel(&u1[1], 1010);
    signel(&u2[1], 1010);
    signel(&u3[1], 1010);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long l = 0; l < NREPS; l++) {
        long nl1 = 1, nl2 = 2;
        for (long kx = 2; kx <= 3; kx++) {
            for (long ky = 2; ky <= N - 1; ky++) {
                du1[ky] = U(u1,nl1,ky+1,kx) - U(u1,nl1,ky-1,kx);
                du2[ky] = U(u2,nl1,ky+1,kx) - U(u2,nl1,ky-1,kx);
                du3[ky] = U(u3,nl1,ky+1,kx) - U(u3,nl1,ky-1,kx);
                U(u1,nl2,ky,kx) = U(u1,nl1,ky,kx)
                    + a11*du1[ky] + a12*du2[ky] + a13*du3[ky]
                    + sig*(U(u1,nl1,ky,kx+1)
                    - 2.0*U(u1,nl1,ky,kx) + U(u1,nl1,ky,kx-1));
                U(u2,nl2,ky,kx) = U(u2,nl1,ky,kx)
                    + a21*du1[ky] + a22*du2[ky] + a23*du3[ky]
                    + sig*(U(u2,nl1,ky,kx+1)
                    - 2.0*U(u2,nl1,ky,kx) + U(u2,nl1,ky,kx-1));
                U(u3,nl2,ky,kx) = U(u3,nl1,ky,kx)
                    + a31*du1[ky] + a32*du2[ky] + a33*du3[ky]
                    + sig*(U(u3,nl1,ky,kx+1)
                    - 2.0*U(u3,nl1,ky,kx) + U(u3,nl1,ky,kx-1));
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("u1(2,51,2) = %f\n", U(u1,2,51,2));
    return 0;
}
