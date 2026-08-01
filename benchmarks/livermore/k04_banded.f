C     Kernel 4 -- Banded linear equations
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K04
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1201), Y(1001)
C
C     Initialize arrays using SIGNEL pattern
C
      SCALED = 0.1D0
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Y(K) = (BUZZ - FIZZ) * SCALED
   10 CONTINUE
C
      N = 1001
      M = (1001 - 7) / 2
C
      DO 200 REP = 1, 11250000
C         Reset X each rep
          FUZZ  = 1.2345D-3
          BUZZ  = 1.0D0 + FUZZ
          FIZZ  = 1.1D0 * FUZZ
          DO 20 K = 1, 1001
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              X(K) = (BUZZ - FIZZ) * SCALED
   20     CONTINUE
C
C         Kernel loop
C         C uses k=6..1000 step m, 0-based; Fortran uses k=7..1001 step m, 1-based
C
          DO 100 K = 7, 1001, M
              LW = K - 6
              TEMP = X(K)
C             C uses j=4..n-1 step 5, 0-based; Fortran uses j=5..n step 5, 1-based
              DO 90 J = 5, N, 5
                  TEMP = TEMP - X(LW) * Y(J)
                  LW = LW + 1
   90         CONTINUE
              X(K) = Y(5) * TEMP
  100     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) X(7)
  900 FORMAT('K4 banded: x(7) = ', E25.15)
      END
