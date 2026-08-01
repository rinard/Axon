C     Kernel 10 -- Difference predictors (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical: PX(25,101), CX(25,101)
C
      PROGRAM K10
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION PX(25,101), CX(25,101)
C
C     Initialize PX in column-major order: J outer, I inner
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 12 J = 1, 101
          DO 10 I = 1, 25
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              PX(I,J) = (BUZZ - FIZZ) * 0.1D0
   10     CONTINUE
   12 CONTINUE
C
C     Initialize CX
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 22 J = 1, 101
          DO 20 I = 1, 25
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              CX(I,J) = (BUZZ - FIZZ) * 0.1D0
   20     CONTINUE
   22 CONTINUE
C
C     Kernel loop
C
      N = 101
      DO 200 REP = 1, 52000000
          DO 90 K = 1, N
              AR       =      CX(5,K)
              BR       = AR - PX(5,K)
              PX(5,K)  = AR
              CR       = BR - PX(6,K)
              PX(6,K)  = BR
              AR       = CR - PX(7,K)
              PX(7,K)  = CR
              BR       = AR - PX(8,K)
              PX(8,K)  = AR
              CR       = BR - PX(9,K)
              PX(9,K)  = BR
              AR       = CR - PX(10,K)
              PX(10,K) = CR
              BR       = AR - PX(11,K)
              PX(11,K) = AR
              CR       = BR - PX(12,K)
              PX(12,K) = BR
              PX(14,K) = CR - PX(13,K)
              PX(13,K) = CR
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) PX(14,1)
  900 FORMAT('px(14,1) = ', E25.15)
      END
