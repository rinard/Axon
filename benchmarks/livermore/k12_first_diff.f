C     Kernel 12 -- First difference
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K12
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), Y(1001)
C
C     Initialize Y using SIGNEL pattern
C
      SCALED = 0.1D0
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Y(K) = (BUZZ - FIZZ) * SCALED
   10 CONTINUE
C
      DO 15 I = 1, 1001
          X(I) = 0.0D0
   15 CONTINUE
C
C     Kernel loop
C
      N = 1000
      DO 200 REP = 1, 35622000
          DO 90 K = 1, N
              X(K) = Y(K+1) - Y(K)
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('K12 first diff: x(1) = ', E25.15)
      END
