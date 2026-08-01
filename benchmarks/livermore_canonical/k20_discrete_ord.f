C     Kernel 20 -- Discrete Ordinates Transport (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body:
C       dw = 0.2
C       DO 20 k=1,n:
C         DI = Y(k) - G(k)/(XX(k)+DK)
C         DN = dw
C         IF (DI .NE. 0.0) DN = MAX(S, MIN(Z(k)/DI, T))
C         X(k) = ((W(k)+V(k)*DN)*XX(k) + U(k))/(VX(k)+V(k)*DN)
C         XX(k+1) = (X(k)-XX(k))*DN + XX(k)
C
      PROGRAM K20
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), Y(1001), Z(1001), U(1001), V(1001), W(1001)
      DIMENSION G(1001), XX(1001), VX(1001)
      DIMENSION SPACER(39)
C
C     Initialize SPACER and pull DK, S, T from canonical positions
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 5 K = 1, 39
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SPACER(K) = (BUZZ - FIZZ) * 0.1D0
    5 CONTINUE
      DK = SPACER(15)
      S  = SPACER(32)
      T  = SPACER(36)
C
C     Initialize arrays X, Y, Z, U, V, W, G, XX, VX using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         X(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Y(K) = (BUZZ - FIZZ) * 0.1D0
   12 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Z(K) = (BUZZ - FIZZ) * 0.1D0
   14 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         U(K) = (BUZZ - FIZZ) * 0.1D0
   16 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         V(K) = (BUZZ - FIZZ) * 0.1D0
   18 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 20 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         W(K) = (BUZZ - FIZZ) * 0.1D0
   20 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         G(K) = (BUZZ - FIZZ) * 0.1D0
   22 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 24 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         XX(K) = (BUZZ - FIZZ) * 0.1D0
   24 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 26 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VX(K) = (BUZZ - FIZZ) * 0.1D0
   26 CONTINUE
C
      N = 1000
      DW = 0.2D0
C
      DO 500 REP = 1, 2260000
         DO 200 K = 1, N
            DI = Y(K) - G(K)/(XX(K) + DK)
            DN = DW
            IF (DI .NE. 0.0D0) THEN
               TMP = Z(K)/DI
               IF (T .LT. TMP) TMP = T
               IF (S .GT. TMP) TMP = S
               DN = TMP
            END IF
            X(K) = ((W(K) + V(K)*DN)*XX(K) + U(K))
     &            /(VX(K) + V(K)*DN)
            XX(K+1) = (X(K) - XX(K))*DN + XX(K)
  200    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) X(N)
  900 FORMAT('x(n) = ', E25.15)
      END
