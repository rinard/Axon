/* K8 -- ADI integration (canonical, 1-based indexing)
   Canonical: U1(5,101,2), U2(5,101,2), U3(5,101,2), DU1/2/3(101)
   Column-major: k1 stride 1, k2 stride 5, k3 stride 5*101=505 */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     100
#define NREPS 22600000

/* 1-based Fortran column-major: U(arr,k1,k2,k3) with dims (5,101,2) */
#define U(arr,k1,k2,k3) arr[((k3)-1)*505 + ((k2)-1)*5 + (k1)]

int main(void) {
    /* Max flat: (2-1)*505 + (101-1)*5 + 5 = 1010, need [1011] */
    double u1[1011], u2[1011], u3[1011];
    double du1[102], du2[102], du3[102];
    double spacer[40];

    signel(spacer+1, 39);
    double a11 = spacer[1], a12 = spacer[2], a13 = spacer[3];
    double a21 = spacer[4], a22 = spacer[5], a23 = spacer[6];
    double a31 = spacer[7], a32 = spacer[8], a33 = spacer[9];
    double sig = spacer[34];

    /* Fill 1010 elements starting at index 1 (column-major storage order) */
    signel(&u1[1], 1010);
    signel(&u2[1], 1010);
    signel(&u3[1], 1010);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (long rep = 0; rep < NREPS; rep++) {
        long nl1 = 1, nl2 = 2;
        double fw = 2.0;
        for (long kx = 2; kx <= 3; kx++) {
            for (long ky = 2; ky <= N; ky++) {
                du1[ky] = U(u1,kx,ky+1,nl1) - U(u1,kx,ky-1,nl1);
                du2[ky] = U(u2,kx,ky+1,nl1) - U(u2,kx,ky-1,nl1);
                du3[ky] = U(u3,kx,ky+1,nl1) - U(u3,kx,ky-1,nl1);
                U(u1,kx,ky,nl2) = U(u1,kx,ky,nl1)
                    + a11*du1[ky] + a12*du2[ky] + a13*du3[ky]
                    + sig*(U(u1,kx+1,ky,nl1) - fw*U(u1,kx,ky,nl1)
                           + U(u1,kx-1,ky,nl1));
                U(u2,kx,ky,nl2) = U(u2,kx,ky,nl1)
                    + a21*du1[ky] + a22*du2[ky] + a23*du3[ky]
                    + sig*(U(u2,kx+1,ky,nl1) - fw*U(u2,kx,ky,nl1)
                           + U(u2,kx-1,ky,nl1));
                U(u3,kx,ky,nl2) = U(u3,kx,ky,nl1)
                    + a31*du1[ky] + a32*du2[ky] + a33*du3[ky]
                    + sig*(U(u3,kx+1,ky,nl1) - fw*U(u3,kx,ky,nl1)
                           + U(u3,kx-1,ky,nl1));
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("u1(2,2,2) = %f\n", U(u1,2,2,2));
    return 0;
}
