C     Kernel 11 -- First sum / partial sums (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: X(1) = Y(1); DO k=2,n: X(k) = X(k-1) + Y(k)
C
      PROGRAM K11
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), Y(1001)
C
C     Initialize Y
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Y(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
      N = 1001
      DO 200 REP = 1, 34000000
          X(1) = Y(1)
          DO 90 K = 2, N
              X(K) = X(K-1) + Y(K)
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) X(N)
  900 FORMAT('x(n) = ', E25.15)
      END
