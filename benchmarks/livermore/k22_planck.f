C     Kernel 22 -- Planckian Distribution
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K22
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION U(1001), V(1001), X(1001), Y(1001), W(1001)
      DIMENSION SPACER(39)
C
C     Initialize SPACER using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 5 K = 1, 39
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SPACER(K) = (BUZZ - FIZZ) * SCALED
    5 CONTINUE
      EXPMAX = SPACER(26)
C
C     Initialize U using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         U(K) = (BUZZ - FIZZ) * SCALED
   10 CONTINUE
C
C     Initialize V using SIGNEL (ensure positive -- used as divisor)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 15 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         V(K) = (BUZZ - FIZZ) * SCALED
         IF (V(K) .LE. 0.0D0) V(K) = 1.0D0
   15 CONTINUE
C
C     Initialize X using SIGNEL (ensure positive for exp-1 divisor)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 20 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         X(K) = (BUZZ - FIZZ) * SCALED
         IF (X(K) .LE. 0.0D0) X(K) = 0.01D0
   20 CONTINUE
C
C     Zero out Y and W
C
      DO 25 K = 1, 1001
         Y(K) = 0.0D0
         W(K) = 0.0D0
   25 CONTINUE
C
      N = 101
C
C     Kernel 22: Planckian Distribution
C
      DO 500 IREP = 1, 48640000
         EXPMAX = 20.0D0
         U(N) = 0.99D0 * EXPMAX * V(N)
         DO 200 K = 1, N
            Y(K) = U(K) / V(K)
            W(K) = X(K) / (DEXP(Y(K)) - 1.0D0)
  200    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) W(51)
  900 FORMAT('K22 planck: w(51) = ', E23.15E3)
      END
