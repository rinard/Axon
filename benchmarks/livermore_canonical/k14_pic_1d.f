C     Kernel 14 -- 1-D Particle in Cell (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: lines 243-264 of the kernels listing.
C     MOD2N(IR(k), 2048) = IAND(IR(k), 2047).
C
      PROGRAM K14
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION VX(1001), XX(1001), XI(1001), EX1(1001), DEX1(1001)
      DIMENSION EX(1001), DEX(1001), GRD(1001), RX(1001), RH(2049)
      INTEGER IX(1001), IR(1001)
      DIMENSION SPACER(39)
C
C     Initialize SPACER and pull FLX from canonical position 27
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 5 K = 1, 39
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SPACER(K) = (BUZZ - FIZZ) * 0.1D0
    5 CONTINUE
      FLX = SPACER(27)
C
C     GRD: valid grid indices in [1.5, 1.5+512)
C
      DO 10 I = 1, 1001
         GRD(I) = DBLE(MOD(I-1, 512)) + 1.5D0
   10 CONTINUE
C
C     Initialize EX, DEX via SIGNEL (independent streams)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 15 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         EX(K) = (BUZZ - FIZZ) * 0.1D0
   15 CONTINUE
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 17 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         DEX(K) = (BUZZ - FIZZ) * 0.1D0
   17 CONTINUE
C
C     Initialize RH via SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 K = 1, 2049
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         RH(K) = (BUZZ - FIZZ) * 0.1D0
   18 CONTINUE
C
C     Zero remaining arrays
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
C
      N  = 1001
      FW = 1.0D0
C
C     Kernel 14 body (verbatim from canonical lines 243-264)
C
      DO 500 REP = 1, 2700000
         DO 141 K = 1, N
            VX(K)   = 0.0D0
            XX(K)   = 0.0D0
            IX(K)   = INT(GRD(K))
            XI(K)   = DBLE(IX(K))
            EX1(K)  = EX(IX(K))
            DEX1(K) = DEX(IX(K))
  141    CONTINUE
C
         DO 142 K = 1, N
            VX(K) = VX(K) + EX1(K) + (XX(K) - XI(K)) * DEX1(K)
            XX(K) = XX(K) + VX(K)  + FLX
            IR(K) = XX(K)
            RX(K) = XX(K) - IR(K)
            IR(K) = IAND(IR(K), 2047) + 1
            XX(K) = RX(K) + IR(K)
  142    CONTINUE
C
         DO 14 K = 1, N
            RH(IR(K))   = RH(IR(K))   + FW - RX(K)
            RH(IR(K)+1) = RH(IR(K)+1) + RX(K)
   14    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) RH(1)
  900 FORMAT('rh(1) = ', E25.15)
      END
