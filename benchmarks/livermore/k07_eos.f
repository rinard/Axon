C     Kernel 7 -- Equation of state fragment
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K07
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), U(1001), Z(1001), Y(1001)
      DIMENSION SPACER(39)
C
C     Initialize spacer for constants
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
C     Initialize U, Z, Y arrays
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          U(K) = (BUZZ - FIZZ) * SCALED
   10 CONTINUE
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 15 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Z(K) = (BUZZ - FIZZ) * SCALED
   15 CONTINUE
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 16 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Y(K) = (BUZZ - FIZZ) * SCALED
   16 CONTINUE
C
      DO 17 I = 1, 1001
          X(I) = 0.0D0
   17 CONTINUE
C
C     Kernel loop
C
      N = 995
      DO 200 REP = 1, 11472000
          DO 90 K = 1, N
              X(K) = U(K) + R*(Z(K) + R*Y(K)) +
     &               T*(U(K+3) + R*(U(K+2) + R*U(K+1)) +
     &                  T*(U(K+6) + Q*(U(K+5) + Q*U(K+4))))
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('K7 EOS: x(1) = ', E25.15)
      END
