C     Kernel 12 -- First difference (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: DO k=1,n: X(k) = Y(k+1) - Y(k)
C
      PROGRAM K12
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1000), Y(1001)
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
      N = 1000
      DO 200 REP = 1, 41000000
          DO 90 K = 1, N
              X(K) = Y(K+1) - Y(K)
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('x(1) = ', E25.15)
      END
