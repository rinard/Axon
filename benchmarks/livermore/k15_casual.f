C     Kernel 15 -- Casual Fortran
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K15
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION VY(101,25), VH(101,7), VF(101,7)
      DIMENSION VG(101,7), VS(101,7)
C
C     Initialize VY using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 12 J = 1, 25
         DO 11 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VY(I,J) = (BUZZ - FIZZ) * SCALED
   11    CONTINUE
   12 CONTINUE
C
C     Initialize VH using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 7
         DO 13 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VH(I,J) = (BUZZ - FIZZ) * SCALED
   13    CONTINUE
   14 CONTINUE
C
C     Initialize VF using SIGNEL (ensure positive -- used as divisor)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 J = 1, 7
         DO 15 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VF(I,J) = (BUZZ - FIZZ) * SCALED
            IF (VF(I,J) .LE. 0.0D0) VF(I,J) = 0.001D0
   15    CONTINUE
   16 CONTINUE
C
C     Initialize VG using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 J = 1, 7
         DO 17 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VG(I,J) = (BUZZ - FIZZ) * SCALED
   17    CONTINUE
   18 CONTINUE
C
C     Initialize VS using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 J = 1, 7
         DO 21 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VS(I,J) = (BUZZ - FIZZ) * SCALED
   21    CONTINUE
   22 CONTINUE
C
C     Kernel 15: Casual Fortran
C     Note: C code uses 0-based indices [j][k] where first dim is "group"
C     and second is "zone". In Fortran original, VY(k,j) with k=zone, j=group.
C     The C ref loops j=1..ng-1, k=1..nz-1 (0-based).
C     In Fortran 1-based: j=2..NG, k=2..NZ
C
      DO 500 IREP = 1, 4249000
         NG = 7
         NZ = 101
         AR = 0.053D0
         BR = 0.073D0
C
         DO 300 J = 2, NG
            DO 200 K = 2, NZ
C
C              Check j+1 > NG (i.e., j >= NG in Fortran 1-based)
               IF (J .GE. NG) THEN
                  VY(K,J) = 0.0D0
                  GO TO 200
               END IF
C
               IF (VH(K,J+1) .GT. VH(K,J)) THEN
                  T = AR
               ELSE
                  T = BR
               END IF
C
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
C
               VY(K,J) = DSQRT(VG(K,J)*VG(K,J) + R*R) * T / S
C
C              Check k+1 > NZ (i.e., k >= NZ in Fortran 1-based)
               IF (K .GE. NZ) THEN
                  VS(K,J) = 0.0D0
                  GO TO 200
               END IF
C
               IF (VF(K,J) .LT. VF(K,J-1)) THEN
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
C
               VS(K,J) = DSQRT(VH(K,J)*VH(K,J) + R*R) * T / S
  200       CONTINUE
  300    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) VY(51,4)
  900 FORMAT('K15 casual: vy(51,4) = ', E23.15E3)
      END
