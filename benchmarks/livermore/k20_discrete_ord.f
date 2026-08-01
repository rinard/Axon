C     Kernel 20 -- Discrete Ordinates Transport
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K20
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION X(1001), Y(1001), Z(1001), W(1001), V(1001)
      DIMENSION U(1001), G(1001), XX(1001), VX(1001)
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
      DK = SPACER(15)
      S  = SPACER(32)
      T  = SPACER(36)
C
C     Initialize arrays using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         X(K) = (BUZZ - FIZZ) * SCALED
   10 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Y(K) = (BUZZ - FIZZ) * SCALED
   12 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Z(K) = (BUZZ - FIZZ) * SCALED
   14 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         W(K) = (BUZZ - FIZZ) * SCALED
   16 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         V(K) = (BUZZ - FIZZ) * SCALED
   18 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 20 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         U(K) = (BUZZ - FIZZ) * SCALED
   20 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         G(K) = (BUZZ - FIZZ) * SCALED
   22 CONTINUE
C
C     Initialize XX using SIGNEL (add 1.0 to ensure nonzero divisor)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 24 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         XX(K) = (BUZZ - FIZZ) * SCALED + 1.0D0
   24 CONTINUE
C
C     Initialize VX using SIGNEL (add 2.0 to ensure nonzero divisor)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 26 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VX(K) = (BUZZ - FIZZ) * SCALED + 2.0D0
   26 CONTINUE
C
      N = 1000
C
C     Kernel 20: Discrete Ordinates Transport
C
      DO 500 IREP = 1, 1570000
C
C        Re-init XX to avoid drift
         FUZZ = 1.2345D-3
         BUZZ = 1.0D0 + FUZZ
         FIZZ = 1.1D0 * FUZZ
         DO 110 K = 1, 1001
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            XX(K) = (BUZZ - FIZZ) * SCALED + 1.0D0
  110    CONTINUE
C
         DO 200 K = 1, N
            DI = Y(K) - G(K)/(XX(K) + DK)
            DN = 0.2D0
            IF (DI .NE. 0.0D0) THEN
               DN = Z(K)/DI
               IF (T .LT. DN) DN = T
               IF (S .GT. DN) DN = S
            END IF
            X(K) = ((W(K) + V(K)*DN)*XX(K) + U(K))
     &            /(VX(K) + V(K)*DN)
            XX(K+1) = (X(K) - XX(K))*DN + XX(K)
  200    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('K20 discrete ord: x(1) = ', E23.15E3)
      END
