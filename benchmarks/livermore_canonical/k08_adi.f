C     Kernel 8 -- ADI integration (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical: U1(5,101,2), U2(5,101,2), U3(5,101,2), DU1/2/3(101)
C
      PROGRAM K08
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION U1(5,101,2), U2(5,101,2), U3(5,101,2)
      DIMENSION DU1(101), DU2(101), DU3(101)
      DIMENSION SPACER(39)
C
C     Initialize SPACER and pull A11..A33, SIG
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 5 K = 1, 39
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          SPACER(K) = (BUZZ - FIZZ) * 0.1D0
    5 CONTINUE
      A11 = SPACER(1)
      A12 = SPACER(2)
      A13 = SPACER(3)
      A21 = SPACER(4)
      A22 = SPACER(5)
      A23 = SPACER(6)
      A31 = SPACER(7)
      A32 = SPACER(8)
      A33 = SPACER(9)
      SIG = SPACER(34)
C
C     Initialize U1 in column-major order: K3 outer, K2 mid, K1 inner
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 12 K3 = 1, 2
          DO 11 K2 = 1, 101
              DO 10 K1 = 1, 5
                  BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
                  FUZZ = -FUZZ
                  U1(K1,K2,K3) = (BUZZ - FIZZ) * 0.1D0
   10         CONTINUE
   11     CONTINUE
   12 CONTINUE
C
C     Initialize U2
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 22 K3 = 1, 2
          DO 21 K2 = 1, 101
              DO 20 K1 = 1, 5
                  BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
                  FUZZ = -FUZZ
                  U2(K1,K2,K3) = (BUZZ - FIZZ) * 0.1D0
   20         CONTINUE
   21     CONTINUE
   22 CONTINUE
C
C     Initialize U3
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 32 K3 = 1, 2
          DO 31 K2 = 1, 101
              DO 30 K1 = 1, 5
                  BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
                  FUZZ = -FUZZ
                  U3(K1,K2,K3) = (BUZZ - FIZZ) * 0.1D0
   30         CONTINUE
   31     CONTINUE
   32 CONTINUE
C
C     Kernel loop
C
      N = 100
      DO 200 REP = 1, 22600000
          NL1 = 1
          NL2 = 2
          FW = 2.0D0
          DO 110 KX = 2, 3
              DO 100 KY = 2, N
                  DU1(KY) = U1(KX,KY+1,NL1) - U1(KX,KY-1,NL1)
                  DU2(KY) = U2(KX,KY+1,NL1) - U2(KX,KY-1,NL1)
                  DU3(KY) = U3(KX,KY+1,NL1) - U3(KX,KY-1,NL1)
                  U1(KX,KY,NL2) = U1(KX,KY,NL1)
     &                + A11*DU1(KY) + A12*DU2(KY) + A13*DU3(KY)
     &                + SIG*(U1(KX+1,KY,NL1) - FW*U1(KX,KY,NL1)
     &                       + U1(KX-1,KY,NL1))
                  U2(KX,KY,NL2) = U2(KX,KY,NL1)
     &                + A21*DU1(KY) + A22*DU2(KY) + A23*DU3(KY)
     &                + SIG*(U2(KX+1,KY,NL1) - FW*U2(KX,KY,NL1)
     &                       + U2(KX-1,KY,NL1))
                  U3(KX,KY,NL2) = U3(KX,KY,NL1)
     &                + A31*DU1(KY) + A32*DU2(KY) + A33*DU3(KY)
     &                + SIG*(U3(KX+1,KY,NL1) - FW*U3(KX,KY,NL1)
     &                       + U3(KX-1,KY,NL1))
  100         CONTINUE
  110     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) U1(2,2,2)
  900 FORMAT('u1(2,2,2) = ', E25.15)
      END
