C     Kernel 14 -- 1-D Particle-in-Cell
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K14
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION VX(1001), XX(1001), XI(1001), EX1(1001), DEX1(1001)
      DIMENSION EX(1001), DEX(1001), GRD(1001), RX(1001), RH(2049)
      INTEGER IX(1001), IR(1001)
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
      FLX = SPACER(27)
C
C     GRD must be valid grid indices
C
      DO 10 I = 1, 1001
         GRD(I) = DBLE(MOD(I-1, 512)) + 1.5D0
   10 CONTINUE
C
C     Initialize EX, DEX using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 15 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         EX(K) = (BUZZ - FIZZ) * SCALED
   15 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 17 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         DEX(K) = (BUZZ - FIZZ) * SCALED
   17 CONTINUE
C
C     Zero out arrays
C
      DO 20 I = 1, 1001
         VX(I)   = 0.0D0
         XX(I)   = 0.0D0
         XI(I)   = 0.0D0
         EX1(I)  = 0.0D0
         DEX1(I) = 0.0D0
         RX(I)   = 0.0D0
         IX(I)   = 0
         IR(I)   = 0
   20 CONTINUE
      DO 25 I = 1, 2049
         RH(I) = 0.0D0
   25 CONTINUE
C
      N = 1001
C
C     Kernel 14: 1-D PIC
C
      DO 500 IREP = 1, 1867000
C
C        Reset RH
         DO 110 I = 1, 2049
            RH(I) = 0.0D0
  110    CONTINUE
C
C        First pass: gather field values
         DO 200 K = 1, N
            VX(K)   = 0.0D0
            XX(K)   = 0.0D0
            IX(K)   = INT(GRD(K))
            XI(K)   = DBLE(IX(K))
            EX1(K)  = EX(IX(K))
            DEX1(K) = DEX(IX(K))
  200    CONTINUE
C
C        Second pass: push particles
         DO 300 K = 1, N
            VX(K) = VX(K) + EX1(K) + (XX(K)-XI(K))*DEX1(K)
            XX(K) = XX(K) + VX(K) + FLX
            IR(K) = INT(XX(K))
            RX(K) = XX(K) - DBLE(IR(K))
            IR(K) = IAND(IR(K), 2047) + 1
            XX(K) = RX(K) + DBLE(IR(K))
  300    CONTINUE
C
C        Third pass: deposit charge
         DO 400 K = 1, N
            RH(IR(K))   = RH(IR(K))   + 1.0D0 - RX(K)
            RH(IR(K)+1) = RH(IR(K)+1) + RX(K)
  400    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) XX(1)
  900 FORMAT('K14 1-D PIC: xx(1) = ', E23.15E3)
      END
