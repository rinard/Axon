C     Kernel 24 -- Find Location of First Minimum (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body:
C       X(n/2) = -1.0d+10
C       m = 1
C       DO 24 k=2,n: IF (X(k) .LT. X(m)) m=k
C
      PROGRAM K24
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP, M
      DIMENSION X(1001)
C
C     Initialize X using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         X(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
      N = 1001
      M = 1
C
      DO 500 REP = 1, 40750000
         X(N/2) = -1.0D+10
         M = 1
         DO 200 K = 2, N
            IF (X(K) .LT. X(M)) M = K
  200    CONTINUE
  500 CONTINUE
C
      WRITE(*,901) M
      WRITE(*,902) X(M)
  901 FORMAT('m = ', I6)
  902 FORMAT('x(m) = ', E25.15)
      END
