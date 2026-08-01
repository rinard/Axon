C     Kernel 9 -- Integrate predictors
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K09
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION PX(101,25)
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
C     C indices (0-based): 15,16,17,18,19,20,21,11
C     Fortran (1-based): 16,17,18,19,20,21,22,12
      DM22 = SPACER(16)
      DM23 = SPACER(17)
      DM24 = SPACER(18)
      DM25 = SPACER(19)
      DM26 = SPACER(20)
      DM27 = SPACER(21)
      DM28 = SPACER(22)
      C0   = SPACER(12)
C
C     Initialize PX using SIGNEL pattern
C     C: px[101][25], stored row-major
C     Fortran: PX(101,25), stored column-major
C
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
C     Kernel loop
C     C uses 0-based column indices; Fortran uses 1-based
C     C: px[i][0] = ... px[i][12] ... px[i][2]
C     F: PX(I,1) = ... PX(I,13) ... PX(I,3)
C
      N = 101
      DO 200 REP = 1, 60639000
          DO 90 I = 1, N
              PX(I,1) = DM28*PX(I,13) + DM27*PX(I,12)
     &                + DM26*PX(I,11) + DM25*PX(I,10)
     &                + DM24*PX(I,9)  + DM23*PX(I,8)
     &                + DM22*PX(I,7)  + C0*(PX(I,5) + PX(I,6))
     &                + PX(I,3)
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) PX(51,1)
  900 FORMAT('K9 integrate pred: px(51,1) = ', E25.15)
      END
