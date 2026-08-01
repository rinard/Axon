C     Kernel 23 -- 2-D Implicit Hydrodynamics (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body:
C       fw = 0.175
C       DO 23 j=2,6; DO 23 k=2,n:
C         QA = ZA(k,j+1)*ZR(k,j) + ZA(k,j-1)*ZB(k,j)
C            + ZA(k+1,j)*ZU(k,j) + ZA(k-1,j)*ZV(k,j) + ZZ(k,j)
C         ZA(k,j) = ZA(k,j) + fw*(QA - ZA(k,j))
C
      PROGRAM K23
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION ZA(101,7), ZB(101,7), ZR(101,7)
      DIMENSION ZU(101,7), ZV(101,7), ZZ(101,7)
C
C     Initialize ZA, ZB, ZR, ZU, ZV, ZZ via SIGNEL (column-major fill)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 J = 1, 7
         DO 11 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZA(I,J) = (BUZZ - FIZZ) * 0.1D0
   11    CONTINUE
   12 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 7
         DO 13 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZB(I,J) = (BUZZ - FIZZ) * 0.1D0
   13    CONTINUE
   14 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 J = 1, 7
         DO 15 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZR(I,J) = (BUZZ - FIZZ) * 0.1D0
   15    CONTINUE
   16 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 J = 1, 7
         DO 17 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZU(I,J) = (BUZZ - FIZZ) * 0.1D0
   17    CONTINUE
   18 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 J = 1, 7
         DO 21 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZV(I,J) = (BUZZ - FIZZ) * 0.1D0
   21    CONTINUE
   22 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 26 J = 1, 7
         DO 25 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZZ(I,J) = (BUZZ - FIZZ) * 0.1D0
   25    CONTINUE
   26 CONTINUE
C
      N = 100
      FW = 0.175D0
C
      DO 500 REP = 1, 8600000
         DO 300 J = 2, 6
            DO 200 K = 2, N
               QA = ZA(K,J+1)*ZR(K,J) + ZA(K,J-1)*ZB(K,J)
     &            + ZA(K+1,J)*ZU(K,J) + ZA(K-1,J)*ZV(K,J) + ZZ(K,J)
               ZA(K,J) = ZA(K,J) + FW*(QA - ZA(K,J))
  200       CONTINUE
  300    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) ZA(51,4)
  900 FORMAT('za(51,4) = ', E25.15)
      END
