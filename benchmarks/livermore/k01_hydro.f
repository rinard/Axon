C     Kernel 1 -- Hydro fragment
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K01
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), Y(1001), Z(1012)
      DIMENSION SPACER(39)
C
C     Initialize arrays using SIGNEL pattern
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 5 K = 1, 39
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          SPACER(K) = (BUZZ - FIZZ) * SCALED
    5 CONTINUE
      Q = SPACER(28)
      R = SPACER(30)
      T = SPACER(36)
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
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 15 K = 1, 1012
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Z(K) = (BUZZ - FIZZ) * SCALED
   15 CONTINUE
C
C     Kernel loop
C
      N = 1001
      DO 100 REP = 1, 26147000
          DO 90 K = 1, N
              X(K) = Q + Y(K) * (R * Z(K+10) + T * Z(K+11))
   90     CONTINUE
  100 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('K1 hydro: x(1) = ', E25.15)
      END
