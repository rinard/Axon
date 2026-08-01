C     Kernel 8 -- ADI integration
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K08
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION U1(2,101,5), U2(2,101,5), U3(2,101,5)
      DIMENSION DU1(101), DU2(101), DU3(101)
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
C     Initialize U1, U2, U3 using SIGNEL pattern
C     C array: u1[2][101][5] = 1010 elements, stored row-major
C     Fortran array: U1(2,101,5) = 1010 elements, stored column-major
C     We fill in storage order (column-major for Fortran)
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 12 K3 = 1, 5
          DO 11 K2 = 1, 101
              DO 10 K1 = 1, 2
                  BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
                  FUZZ = -FUZZ
                  U1(K1,K2,K3) = (BUZZ - FIZZ) * SCALED
   10         CONTINUE
   11     CONTINUE
   12 CONTINUE
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 22 K3 = 1, 5
          DO 21 K2 = 1, 101
              DO 20 K1 = 1, 2
                  BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
                  FUZZ = -FUZZ
                  U2(K1,K2,K3) = (BUZZ - FIZZ) * SCALED
   20         CONTINUE
   21     CONTINUE
   22 CONTINUE
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 32 K3 = 1, 5
          DO 31 K2 = 1, 101
              DO 30 K1 = 1, 2
                  BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
                  FUZZ = -FUZZ
                  U3(K1,K2,K3) = (BUZZ - FIZZ) * SCALED
   30         CONTINUE
   31     CONTINUE
   32 CONTINUE
C
C     Kernel loop
C     C: nl1=0,nl2=1 (0-based) -> Fortran: NL1=1,NL2=2 (1-based)
C     C: kx=1..2 (0-based) -> Fortran: KX=2..3 (1-based)
C     C: ky=1..n-2 (0-based) -> Fortran: KY=2..N-1 (1-based)
C
      N = 100
      DO 200 REP = 1, 10535000
          NL1 = 1
          NL2 = 2
          DO 110 KX = 2, 3
              DO 100 KY = 2, N - 1
                  DU1(KY) = U1(NL1,KY+1,KX) - U1(NL1,KY-1,KX)
                  DU2(KY) = U2(NL1,KY+1,KX) - U2(NL1,KY-1,KX)
                  DU3(KY) = U3(NL1,KY+1,KX) - U3(NL1,KY-1,KX)
                  U1(NL2,KY,KX) = U1(NL1,KY,KX)
     &                + A11*DU1(KY) + A12*DU2(KY) + A13*DU3(KY)
     &                + SIG*(U1(NL1,KY,KX+1)
     &                - 2.0D0*U1(NL1,KY,KX) + U1(NL1,KY,KX-1))
                  U2(NL2,KY,KX) = U2(NL1,KY,KX)
     &                + A21*DU1(KY) + A22*DU2(KY) + A23*DU3(KY)
     &                + SIG*(U2(NL1,KY,KX+1)
     &                - 2.0D0*U2(NL1,KY,KX) + U2(NL1,KY,KX-1))
                  U3(NL2,KY,KX) = U3(NL1,KY,KX)
     &                + A31*DU1(KY) + A32*DU2(KY) + A33*DU3(KY)
     &                + SIG*(U3(NL1,KY,KX+1)
     &                - 2.0D0*U3(NL1,KY,KX) + U3(NL1,KY,KX-1))
  100         CONTINUE
  110     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) U1(2,51,2)
  900 FORMAT('K8 ADI: u1(2,51,2) = ', E25.15)
      END
