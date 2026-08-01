C     Kernel 9 -- Integrate predictors (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical: PX(25,101)
C       PX(1,k) = DM28*PX(13,k) + DM27*PX(12,k) + DM26*PX(11,k)
C               + DM25*PX(10,k) + DM24*PX(9,k)  + DM23*PX(8,k)
C               + DM22*PX(7,k)  + C0*(PX(5,k) + PX(6,k)) + PX(3,k)
C
      PROGRAM K09
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION PX(25,101)
      DIMENSION SPACER(39)
C
C     Initialize SPACER and pull C0, DM22..DM28
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 5 K = 1, 39
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          SPACER(K) = (BUZZ - FIZZ) * 0.1D0
    5 CONTINUE
      C0   = SPACER(12)
      DM22 = SPACER(16)
      DM23 = SPACER(17)
      DM24 = SPACER(18)
      DM25 = SPACER(19)
      DM26 = SPACER(20)
      DM27 = SPACER(21)
      DM28 = SPACER(22)
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
C     Kernel loop
C
      N = 101
      DO 200 REP = 1, 77700000
          DO 90 K = 1, N
              PX(1,K) = DM28*PX(13,K) + DM27*PX(12,K)
     &                + DM26*PX(11,K) + DM25*PX(10,K)
     &                + DM24*PX(9,K)  + DM23*PX(8,K)
     &                + DM22*PX(7,K)
     &                + C0*(PX(5,K) + PX(6,K))
     &                + PX(3,K)
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) PX(1,1)
  900 FORMAT('px(1,1) = ', E25.15)
      END
