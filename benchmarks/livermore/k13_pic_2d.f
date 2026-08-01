C     Kernel 13 -- 2-D Particle-in-Cell
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K13
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION P(64,4)
      DIMENSION B(64,64), C(64,64), H(64,64)
      DIMENSION Y(1001), Z(1001)
      INTEGER E(96), F(96)
C
C     Initialize particle array: DS = 1.0, DW = 0.5
C
      DS = 1.0D0
      DW = 0.5D0
      DO 5 J = 1, 4
         DO 4 K = 1, 64
            P(K,J) = DS
            DS = DS + DW
    4    CONTINUE
    5 CONTINUE
C
C     Initialize B, C arrays using SIGNEL pattern
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 12 J = 1, 64
         DO 11 I = 1, 64
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            B(I,J) = (BUZZ - FIZZ) * SCALED
   11    CONTINUE
   12 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 64
         DO 13 I = 1, 64
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            C(I,J) = (BUZZ - FIZZ) * SCALED
   13    CONTINUE
   14 CONTINUE
C
C     Initialize H to zero
C
      DO 16 J = 1, 64
         DO 15 I = 1, 64
            H(I,J) = 0.0D0
   15    CONTINUE
   16 CONTINUE
C
C     Initialize Y, Z arrays using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 20 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Y(K) = (BUZZ - FIZZ) * SCALED
   20 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 25 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         Z(K) = (BUZZ - FIZZ) * SCALED
   25 CONTINUE
C
C     Initialize E, F index arrays
C
      DO 30 I = 1, 96
         E(I) = MOD(I-1, 64)
         F(I) = MOD(I-1, 64)
   30 CONTINUE
C
      N = 64
C
C     Kernel 13: 2-D PIC (Particle-in-Cell)
C
      DO 500 IREP = 1, 2570000
C
C        Re-init particles each rep to avoid drift
         DS = 1.0D0
         DW = 0.5D0
         DO 105 J = 1, 4
            DO 104 K = 1, 64
               P(K,J) = DS
               DS = DS + DW
  104       CONTINUE
  105    CONTINUE
C
C        Reset H
         DO 112 J = 1, 64
            DO 111 I = 1, 64
               H(I,J) = 0.0D0
  111       CONTINUE
  112    CONTINUE
C
         DO 200 IP = 1, N
            I1 = INT(P(IP,1))
            J1 = INT(P(IP,2))
            I1 = IAND(I1, 63)
            J1 = IAND(J1, 63)
C           Fortran is 1-based, so add 1 for array access
            P(IP,3) = P(IP,3) + B(I1+1,J1+1)
            P(IP,4) = P(IP,4) + C(I1+1,J1+1)
            P(IP,1) = P(IP,1) + P(IP,3)
            P(IP,2) = P(IP,2) + P(IP,4)
            I2 = INT(P(IP,1))
            J2 = INT(P(IP,2))
            I2 = IAND(I2, 63) - 1
            J2 = IAND(J2, 63) - 1
            P(IP,1) = P(IP,1) + Y(I2+32)
            P(IP,2) = P(IP,2) + Z(J2+32)
            I2 = I2 + E(I2+32)
            J2 = J2 + F(J2+32)
C           Use I2+1, J2+1 for 1-based H
            H(I2+1,J2+1) = H(I2+1,J2+1) + 1.0D0
  200    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) P(1,1)
  900 FORMAT('K13 2-D PIC: p(1,1) = ', E23.15E3)
      END
