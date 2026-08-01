C     Kernel 7 -- Equation of state fragment (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body:
C       X(k) = U(k) + R*(Z(k) + R*Y(k))
C            + T*(U(k+3) + R*(U(k+2) + R*U(k+1))
C            + T*(U(k+6) + Q*(U(k+5) + Q*U(k+4))))
C
      PROGRAM K07
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), U(1001), Z(1001), Y(1001)
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
C     Initialize U
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          U(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
C     Initialize Z
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 15 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Z(K) = (BUZZ - FIZZ) * 0.1D0
   15 CONTINUE
C
C     Initialize Y
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 20 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Y(K) = (BUZZ - FIZZ) * 0.1D0
   20 CONTINUE
C
C     Kernel loop
C
      N = 995
      DO 200 REP = 1, 17000000
          DO 90 K = 1, N
              X(K) = U(K) + R*(Z(K) + R*Y(K)) +
     &               T*(U(K+3) + R*(U(K+2) + R*U(K+1)) +
     &                  T*(U(K+6) + Q*(U(K+5) + Q*U(K+4))))
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('x(1) = ', E25.15)
      END
