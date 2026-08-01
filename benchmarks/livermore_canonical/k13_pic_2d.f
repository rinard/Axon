C     Kernel 13 -- 2-D Particle in Cell (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: lines 211-231 of the original kernels listing.
C     MOD2N(i,j) = IAND(i, j-1).
C     Note: H is over-allocated to 128x128 to fit canonical's i2,j2 range
C     (i2,j2 may exceed 64 after the "i2 = i2 + E(i2+32)" step).
C
      PROGRAM K13
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION P(4,64)
      DIMENSION B(64,64), C(64,64), H(128,128)
      DIMENSION Y(1001), Z(1001)
      INTEGER E(96), F(96)
C
C     Initialize P via DS=1.0, DW=0.5 ramp (j outer, k inner)
C
      DS = 1.0D0
      DW = 0.5D0
      DO 5 J = 1, 4
         DO 4 K = 1, 64
            P(J,K) = DS
            DS = DS + DW
    4    CONTINUE
    5 CONTINUE
C
C     Initialize B using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 J = 1, 64
         DO 11 I = 1, 64
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            B(I,J) = (BUZZ - FIZZ) * 0.1D0
   11    CONTINUE
   12 CONTINUE
C
C     Initialize C using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 64
         DO 113 I = 1, 64
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            C(I,J) = (BUZZ - FIZZ) * 0.1D0
  113    CONTINUE
   14 CONTINUE
C
C     Zero H
C
      DO 16 J = 1, 128
         DO 15 I = 1, 128
            H(I,J) = 0.0D0
   15    CONTINUE
   16 CONTINUE
C
C     Initialize Y using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 20 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Y(K) = (BUZZ - FIZZ) * 0.1D0
   20 CONTINUE
C
C     Initialize Z using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 25 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Z(K) = (BUZZ - FIZZ) * 0.1D0
   25 CONTINUE
C
C     Initialize E, F (mod-64 pattern)
C
      DO 30 I = 1, 96
         E(I) = MOD(I-1, 64)
         F(I) = MOD(I-1, 64)
   30 CONTINUE
C
      N = 64
      FW = 1.0D0
C
C     Kernel 13 body (verbatim from canonical lines 213-231)
C
      DO 500 REP = 1, 33800000
         DO 13 K = 1, N
            I1 = P(1,K)
            J1 = P(2,K)
            I1 = 1 + IAND(I1, 63)
            J1 = 1 + IAND(J1, 63)
            P(3,K) = P(3,K) + B(I1,J1)
            P(4,K) = P(4,K) + C(I1,J1)
            P(1,K) = P(1,K) + P(3,K)
            P(2,K) = P(2,K) + P(4,K)
            I2 = P(1,K)
            J2 = P(2,K)
            I2 = IAND(I2, 63)
            J2 = IAND(J2, 63)
            P(1,K) = P(1,K) + Y(I2+32)
            P(2,K) = P(2,K) + Z(J2+32)
            I2 = I2 + E(I2+32)
            J2 = J2 + F(J2+32)
            H(I2,J2) = H(I2,J2) + FW
   13    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) P(1,1)
  900 FORMAT('p(1,1) = ', E25.15)
      END
