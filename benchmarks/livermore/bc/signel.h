/* SIGNEL — Livermore Loops data generator
   Generates "friendly" floating-point numbers near 0.1 (SCALE=0.1, BIAS=0.0).
   Transcribed from the original Fortran in UCRL-53745. */

#ifndef SIGNEL_H
#define SIGNEL_H

static void signel(double *v, long n) {
    double fuzz  = 1.2345e-3;
    double buzz  = 1.0 + fuzz;
    double fizz  = 1.1 * fuzz;
    double scaled = 0.1;
    for (long k = 0; k < n; k++) {
        buzz = (1.0 - fuzz) * buzz + fuzz;
        fuzz = -fuzz;
        v[k] = (buzz - fizz) * scaled;
    }
}

/* Fill particle array P[512][4] with original Fortran values:
   DS = 1.0, DW = 0.5, P(j,k) = DS; DS = DS + DW
   In column-major (Fortran) order: j=1..4, k=1..512 */
static void init_particles(double *p, long np) {
    double ds = 1.0, dw = 0.5;
    for (long j = 0; j < 4; j++) {
        for (long k = 0; k < np; k++) {
            p[k * 4 + j] = ds;  /* p[k][j] in C row-major */
            ds += dw;
        }
    }
}

#endif
