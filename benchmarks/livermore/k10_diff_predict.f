C     Kernel 10 -- Difference predictors
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K10
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION PX(101,25), CX(101,25)
C
C     Initialize PX using SIGNEL pattern
C
      SCALED = 0.1D0
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 12 J = 1, 25
          DO 10 I = 1, 101
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              PX(I,J) = (BUZZ - FIZZ) * SCALED
   10     CONTINUE
   12 CONTINUE
C
C     Initialize CX using SIGNEL pattern
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 22 J = 1, 25
          DO 20 I = 1, 101
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              CX(I,J) = (BUZZ - FIZZ) * SCALED
   20     CONTINUE
   22 CONTINUE
C
C     Kernel loop
C     C 0-based col indices -> Fortran 1-based: col+1
C     C: cx[i][4]->CX(I,5), px[i][4]->PX(I,5), etc.
C
      N = 101
      DO 200 REP = 1, 48656000
          DO 90 I = 1, N
              AR       =     CX(I,5)
              BR       = AR - PX(I,5)
              PX(I,5)  = AR
              CR       = BR - PX(I,6)
              PX(I,6)  = BR
              AR       = CR - PX(I,7)
              PX(I,7)  = CR
              BR       = AR - PX(I,8)
              PX(I,8)  = AR
              CR       = BR - PX(I,9)
              PX(I,9)  = BR
              AR       = CR - PX(I,10)
              PX(I,10) = CR
              BR       = AR - PX(I,11)
              PX(I,11) = AR
              CR       = BR - PX(I,12)
              PX(I,12) = BR
              PX(I,14) = CR - PX(I,13)
              PX(I,13) = CR
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) PX(51,5)
  900 FORMAT('K10 diff pred: px(51,5) = ', E25.15)
      END
