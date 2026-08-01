C     Kernel 18 -- 2-D explicit hydrodynamics fragment (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: lines 438-466 of the kernels listing.
C     T=0.0037, S=0.0041 hardcoded in canonical pre-loop.
C     JN set to n-1 (=100) so j+1 access stays within 101-wide fast dim.
C     ZM gets +10 offset to keep divisor bounded away from 0.
C
      PROGRAM K18
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION ZA(101,7), ZB(101,7), ZP(101,7), ZQ(101,7)
      DIMENSION ZR(101,7), ZM(101,7), ZU(101,7), ZV(101,7), ZZ(101,7)
C
C     ZP via SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 J = 1, 7
         DO 11 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZP(I,J) = (BUZZ - FIZZ) * 0.1D0
   11    CONTINUE
   12 CONTINUE
C
C     ZQ via SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 7
         DO 13 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZQ(I,J) = (BUZZ - FIZZ) * 0.1D0
   13    CONTINUE
   14 CONTINUE
C
C     ZR via SIGNEL
C
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
C
C     ZM via SIGNEL + 10 (avoid divisor near zero)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 18 J = 1, 7
         DO 17 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZM(I,J) = (BUZZ - FIZZ) * 0.1D0 + 10.0D0
   17    CONTINUE
   18 CONTINUE
C
C     ZZ via SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 22 J = 1, 7
         DO 21 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            ZZ(I,J) = (BUZZ - FIZZ) * 0.1D0
   21    CONTINUE
   22 CONTINUE
C
C     Zero ZA, ZB, ZU, ZV
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
      N = 101
C
C     Kernel 18 body (canonical lines 438-466)
C
      DO 500 REP = 1, 3840000
         T  = 0.003700D0
         S  = 0.004100D0
         KN = 6
         JN = N - 1
         DO 70 K = 2, KN
            DO 170 J = 2, JN
               ZA(J,K) = (ZP(J-1,K+1)+ZQ(J-1,K+1)
     &                    -ZP(J-1,K)-ZQ(J-1,K))
     &                  * (ZR(J,K)+ZR(J-1,K))
     &                  / (ZM(J-1,K)+ZM(J-1,K+1))
               ZB(J,K) = (ZP(J-1,K)+ZQ(J-1,K)
     &                    -ZP(J,K)-ZQ(J,K))
     &                  * (ZR(J,K)+ZR(J,K-1))
     &                  / (ZM(J,K)+ZM(J-1,K))
  170       CONTINUE
   70    CONTINUE
C
         DO 72 K = 2, KN
            DO 172 J = 2, JN
               ZU(J,K) = ZU(J,K) + S*(ZA(J,K)*(ZZ(J,K)-ZZ(J+1,K))
     &                              -ZA(J-1,K)*(ZZ(J,K)-ZZ(J-1,K))
     &                              -ZB(J,K)*(ZZ(J,K)-ZZ(J,K-1))
     &                              +ZB(J,K+1)*(ZZ(J,K)-ZZ(J,K+1)))
               ZV(J,K) = ZV(J,K) + S*(ZA(J,K)*(ZR(J,K)-ZR(J+1,K))
     &                              -ZA(J-1,K)*(ZR(J,K)-ZR(J-1,K))
     &                              -ZB(J,K)*(ZR(J,K)-ZR(J,K-1))
     &                              +ZB(J,K+1)*(ZR(J,K)-ZR(J,K+1)))
  172       CONTINUE
   72    CONTINUE
C
         DO 75 K = 2, KN
            DO 175 J = 2, JN
               ZR(J,K) = ZR(J,K) + T*ZU(J,K)
               ZZ(J,K) = ZZ(J,K) + T*ZV(J,K)
  175       CONTINUE
   75    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) ZU(51,4)
  900 FORMAT('zu(51,4) = ', E25.15)
      END
