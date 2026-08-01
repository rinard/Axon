C     Kernel 23 -- 2-D Implicit Hydrodynamics
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K23
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION ZA(101,7), ZR(101,7), ZB(101,7)
      DIMENSION ZU(101,7), ZV(101,7), ZZ(101,7)
C
C     Initialize ZA using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 12 J = 1, 7
         DO 11 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZA(I,J) = (BUZZ - FIZZ) * SCALED
   11    CONTINUE
   12 CONTINUE
C
C     Initialize ZR using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 7
         DO 13 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZR(I,J) = (BUZZ - FIZZ) * SCALED
   13    CONTINUE
   14 CONTINUE
C
C     Initialize ZB using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 J = 1, 7
         DO 15 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZB(I,J) = (BUZZ - FIZZ) * SCALED
   15    CONTINUE
   16 CONTINUE
C
C     Initialize ZU using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 J = 1, 7
         DO 17 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZU(I,J) = (BUZZ - FIZZ) * SCALED
   17    CONTINUE
   18 CONTINUE
C
C     Initialize ZV using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 J = 1, 7
         DO 21 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZV(I,J) = (BUZZ - FIZZ) * SCALED
   21    CONTINUE
   22 CONTINUE
C
C     Initialize ZZ using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 26 J = 1, 7
         DO 25 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZZ(I,J) = (BUZZ - FIZZ) * SCALED
   25    CONTINUE
   26 CONTINUE
C
      N = 100
C
C     Kernel 23: 2-D Implicit Hydrodynamics (Jacobi relaxation)
C     C code loops j=1..5, k=1..n-1 (0-based).
C     In Fortran 1-based: J=2..6, K=2..N
C
      DO 500 IREP = 1, 8581000
         DO 300 J = 2, 6
            DO 200 K = 2, N
               QA = ZA(K,J+1)*ZR(K,J) + ZA(K,J-1)*ZB(K,J)
     &            + ZA(K+1,J)*ZU(K,J) + ZA(K-1,J)*ZV(K,J) + ZZ(K,J)
               ZA(K,J) = ZA(K,J) + 0.175D0*(QA - ZA(K,J))
  200       CONTINUE
  300    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) ZA(51,4)
  900 FORMAT('K23 hydro implicit: za(51,4) = ', E23.15E3)
      END
