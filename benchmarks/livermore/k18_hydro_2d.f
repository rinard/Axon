C     Kernel 18 -- 2-D Explicit Hydrodynamics
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K18
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION ZA(101,7), ZP(101,7), ZQ(101,7), ZR(101,7)
      DIMENSION ZM(101,7), ZB(101,7), ZU(101,7), ZV(101,7), ZZ(101,7)
C
C     Initialize ZP using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 12 J = 1, 7
         DO 11 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZP(I,J) = (BUZZ - FIZZ) * SCALED
   11    CONTINUE
   12 CONTINUE
C
C     Initialize ZQ using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 7
         DO 13 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZQ(I,J) = (BUZZ - FIZZ) * SCALED
   13    CONTINUE
   14 CONTINUE
C
C     Initialize ZR using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 16 J = 1, 7
         DO 15 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZR(I,J) = (BUZZ - FIZZ) * SCALED
   15    CONTINUE
   16 CONTINUE
C
C     Initialize ZM using SIGNEL (add 10.0 to ensure large enough for division)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 J = 1, 7
         DO 17 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZM(I,J) = (BUZZ - FIZZ) * SCALED + 10.0D0
   17    CONTINUE
   18 CONTINUE
C
C     Initialize ZZ using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 J = 1, 7
         DO 21 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZZ(I,J) = (BUZZ - FIZZ) * SCALED
   21    CONTINUE
   22 CONTINUE
C
C     Zero out ZA, ZB, ZU, ZV
C
      DO 26 J = 1, 7
         DO 25 I = 1, 101
            ZA(I,J) = 0.0D0
            ZB(I,J) = 0.0D0
            ZU(I,J) = 0.0D0
            ZV(I,J) = 0.0D0
   25    CONTINUE
   26 CONTINUE
C
C     Kernel 18: 2-D Explicit Hydrodynamics
C     C code uses 0-based [k][j] with k=row, j=col.
C     In Fortran 1-based: ZA(J,K) etc. with J=col=2..JN, K=row=2..KN
C
      DO 500 IREP = 1, 1382000
         T  = 0.0037D0
         S  = 0.0041D0
         KN = 6
         JN = 100
C
C        First loop: compute ZA and ZB
         DO 120 K = 2, KN
            DO 110 J = 2, JN
               ZA(J,K) = (ZP(J-1,K+1)+ZQ(J-1,K+1)
     &                   -ZP(J-1,K)-ZQ(J-1,K))
     &                  *(ZR(J,K)+ZR(J-1,K))
     &                  /(ZM(J-1,K)+ZM(J-1,K+1))
               ZB(J,K) = (ZP(J-1,K)+ZQ(J-1,K)
     &                   -ZP(J,K)-ZQ(J,K))
     &                  *(ZR(J,K)+ZR(J,K-1))
     &                  /(ZM(J,K)+ZM(J-1,K))
  110       CONTINUE
  120    CONTINUE
C
C        Second loop: update ZU and ZV
         DO 220 K = 2, KN
            DO 210 J = 2, JN
               ZU(J,K) = ZU(J,K)
     &           + S*(ZA(J,K)*(ZZ(J,K)-ZZ(J+1,K))
     &               -ZA(J-1,K)*(ZZ(J,K)-ZZ(J-1,K))
     &               -ZB(J,K)*(ZZ(J,K)-ZZ(J,K-1))
     &               +ZB(J,K+1)*(ZZ(J,K)-ZZ(J,K+1)))
               ZV(J,K) = ZV(J,K)
     &           + S*(ZA(J,K)*(ZR(J,K)-ZR(J+1,K))
     &               -ZA(J-1,K)*(ZR(J,K)-ZR(J-1,K))
     &               -ZB(J,K)*(ZR(J,K)-ZR(J,K-1))
     &               +ZB(J,K+1)*(ZR(J,K)-ZR(J,K+1)))
  210       CONTINUE
  220    CONTINUE
C
C        Third loop: update ZR and ZZ
         DO 320 K = 2, KN
            DO 310 J = 2, JN
               ZR(J,K) = ZR(J,K) + T*ZU(J,K)
               ZZ(J,K) = ZZ(J,K) + T*ZV(J,K)
  310       CONTINUE
  320    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) ZU(51,4)
  900 FORMAT('K18 hydro 2D: zu(51,4) = ', E23.15E3)
      END
