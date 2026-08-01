C     Kernel 22 -- Planckian Distribution (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body:
C       EXPMAX = 20.0
C       fw = 1.0
C       U(n) = 0.99*EXPMAX*V(n)
C       DO 22 k=1,n:
C         Y(k) = U(k)/V(k)
C         W(k) = X(k)/(EXP(Y(k)) - fw)
C
      PROGRAM K22
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION U(101), V(101), W(101), X(101), Y(101)
C
C     Initialize U using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         U(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
C     Initialize V using SIGNEL (replace V(K)<=0 with 1.0 -- divisor)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 15 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         V(K) = (BUZZ - FIZZ) * 0.1D0
         IF (V(K) .LE. 0.0D0) V(K) = 1.0D0
   15 CONTINUE
C
C     Initialize X using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 20 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         X(K) = (BUZZ - FIZZ) * 0.1D0
   20 CONTINUE
C
C     Zero Y and W
C
      DO 25 K = 1, 101
         Y(K) = 0.0D0
         W(K) = 0.0D0
   25 CONTINUE
C
      N = 101
C
      DO 500 REP = 1, 51900000
         EXPMAX = 20.0D0
         FW = 1.0D0
         U(N) = 0.99D0 * EXPMAX * V(N)
         DO 200 K = 1, N
            Y(K) = U(K) / V(K)
            W(K) = X(K) / (DEXP(Y(K)) - FW)
  200    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) W(51)
  900 FORMAT('w(51) = ', E25.15)
      END
