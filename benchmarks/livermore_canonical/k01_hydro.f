C     Kernel 1 -- Hydro fragment (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: X(k) = Q + Y(k) * (R*ZX(k+10) + T*ZX(k+11))
C
      PROGRAM K01
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), Y(1001), Z(1012)
      DIMENSION SPACER(39)
C
C     Initialize SPACER and pull Q, R, T from canonical positions
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 5 K = 1, 39
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          SPACER(K) = (BUZZ - FIZZ) * 0.1D0
    5 CONTINUE
      Q = SPACER(28)
      R = SPACER(30)
      T = SPACER(36)
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
C     Initialize Z (acts as ZX)
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 15 K = 1, 1012
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Z(K) = (BUZZ - FIZZ) * 0.1D0
   15 CONTINUE
C
C     Kernel loop
C
      N = 1001
      DO 100 REP = 1, 38000000
          DO 90 K = 1, N
              X(K) = Q + Y(K) * (R * Z(K+10) + T * Z(K+11))
   90     CONTINUE
  100 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('x(1) = ', E25.15)
      END
