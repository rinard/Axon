C     Kernel 17 -- Implicit conditional computation (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: lines 394-427 of the kernels listing.
C     dw, fw, tw set locally in the kernel (no spacer).
C
      PROGRAM K17
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION VSP(101), VSTP(101), VXNE(101), VXND(101)
      DIMENSION VE3(101), VLR(101), VLIN(101)
C
C     All arrays via SIGNEL (independent streams)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 11 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VSP(K) = (BUZZ - FIZZ) * 0.1D0
   11 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VSTP(K) = (BUZZ - FIZZ) * 0.1D0
   12 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 13 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VXNE(K) = (BUZZ - FIZZ) * 0.1D0
   13 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VXND(K) = (BUZZ - FIZZ) * 0.1D0
   14 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 15 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VE3(K) = (BUZZ - FIZZ) * 0.1D0
   15 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VLR(K) = (BUZZ - FIZZ) * 0.1D0
   16 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 17 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         VLIN(K) = (BUZZ - FIZZ) * 0.1D0
   17 CONTINUE
C
      N = 101
C
C     Kernel 17 body (verbatim from canonical lines 394-427)
C
      DO 500 REP = 1, 66400000
         DW    = 5.0000D0 / 3.0000D0
         FW    = 1.0000D0 / 3.0000D0
         TW    = 1.0300D0 / 3.0700D0
         K     = N
         J     = 1
         INK   = -1
         SCALE = DW
         XNM   = FW
         E6    = TW
         GO TO 61
C                                            STEP MODEL
   60    E6      = XNM*VSP(K) + VSTP(K)
         VXNE(K) = E6
         XNM     = E6
         VE3(K)  = E6
         K       = K + INK
         IF (K .EQ. J) GO TO 62
   61    E3      = XNM*VLR(K) + VLIN(K)
         XNEI    = VXNE(K)
         VXND(K) = E6
         XNC     = SCALE * E3
C                                            SELECT MODEL
         IF (XNM  .GT. XNC) GO TO 60
         IF (XNEI .GT. XNC) GO TO 60
C                                            LINEAR MODEL
         VE3(K)  = E3
         E6      = E3 + E3 - XNM
         VXNE(K) = E3 + E3 - XNEI
         XNM     = E6
         K       = K + INK
         IF (K .NE. J) GO TO 61
   62    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) VXNE(N)
  900 FORMAT('vxne(n) = ', E25.15)
      END
