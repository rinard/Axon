C     Kernel 3 -- Inner product (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: Q = 0; DO k=1,n: Q = Q + Z(k)*X(k)
C
      PROGRAM K03
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION Z(1001), X(1001)
C
C     Initialize Z
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Z(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
C     Initialize X
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 20 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          X(K) = (BUZZ - FIZZ) * 0.1D0
   20 CONTINUE
C
C     Kernel loop
C
      N = 1001
      DO 100 REP = 1, 27000000
          Q = 0.0D0
          DO 90 K = 1, N
              Q = Q + Z(K) * X(K)
   90     CONTINUE
  100 CONTINUE
C
      WRITE(*,900) Q
  900 FORMAT('q = ', E25.15)
      END
