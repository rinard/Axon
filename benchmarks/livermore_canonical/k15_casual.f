C     Kernel 15 -- Casual Fortran (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: lines 297-329 of the kernels listing.
C     AR=0.053, BR=0.073 are hardcoded in the canonical pre-loop.
C
      PROGRAM K15
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION VY(101,7), VH(101,7), VF(101,7)
      DIMENSION VG(101,7), VS(101,7)
C
C     VH via SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 7
         DO 13 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VH(I,J) = (BUZZ - FIZZ) * 0.1D0
   13    CONTINUE
   14 CONTINUE
C
C     VF via SIGNEL (must be > 0 -- divisor); replace nonpositive with 0.001
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 J = 1, 7
         DO 15 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VF(I,J) = (BUZZ - FIZZ) * 0.1D0
            IF (VF(I,J) .LE. 0.0D0) VF(I,J) = 0.001D0
   15    CONTINUE
   16 CONTINUE
C
C     VG via SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 J = 1, 7
         DO 17 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VG(I,J) = (BUZZ - FIZZ) * 0.1D0
   17    CONTINUE
   18 CONTINUE
C
C     VS via SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 J = 1, 7
         DO 21 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VS(I,J) = (BUZZ - FIZZ) * 0.1D0
   21    CONTINUE
   22 CONTINUE
C
C     Zero VY (canonical writes VY but never reads it before writing)
C
      DO 26 J = 1, 7
         DO 25 I = 1, 101
            VY(I,J) = 0.0D0
   25    CONTINUE
   26 CONTINUE
C
      N = 101
C
C     Kernel 15 body (verbatim from canonical lines 297-329)
C     Arithmetic IFs translated to cascaded IF/THEN/ELSE.
C
      DO 500 REP = 1, 6600000
         NG = 7
         NZ = N
         AR = 0.053D0
         BR = 0.073D0
         DO 45 J = 2, NG
            DO 145 K = 2, NZ
C              Arith IF on (j - NG): neg -> 31, zero/pos -> 30
               IF (J .LT. NG) GO TO 31
               VY(K,J) = 0.0D0
               GO TO 45
   31          IF (VH(K,J+1) .GT. VH(K,J)) THEN
                  T = AR
               ELSE
                  T = BR
               END IF
               IF (VF(K,J) .LT. VF(K-1,J)) THEN
                  IF (VH(K-1,J) .GT. VH(K-1,J+1)) THEN
                     R = VH(K-1,J)
                  ELSE
                     R = VH(K-1,J+1)
                  END IF
                  S = VF(K-1,J)
               ELSE
                  IF (VH(K,J) .GT. VH(K,J+1)) THEN
                     R = VH(K,J)
                  ELSE
                     R = VH(K,J+1)
                  END IF
                  S = VF(K,J)
               END IF
               VY(K,J) = SQRT(VG(K,J)*VG(K,J) + R*R) * T / S
C              Arith IF on (k - NZ): neg -> 40, zero/pos -> 39
               IF (K .LT. NZ) GO TO 40
               VS(K,J) = 0.0D0
               GO TO 45
   40          IF (VF(K,J) .LT. VF(K,J-1)) THEN
                  IF (VG(K,J-1) .GT. VG(K+1,J-1)) THEN
                     R = VG(K,J-1)
                  ELSE
                     R = VG(K+1,J-1)
                  END IF
                  S = VF(K,J-1)
                  T = BR
               ELSE
                  IF (VG(K,J) .GT. VG(K+1,J)) THEN
                     R = VG(K,J)
                  ELSE
                     R = VG(K+1,J)
                  END IF
                  S = VF(K,J)
                  T = AR
               END IF
               VS(K,J) = SQRT(VH(K,J)*VH(K,J) + R*R) * T / S
  145       CONTINUE
   45    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) VY(2,2)
  900 FORMAT('vy(2,2) = ', E25.15)
      END
