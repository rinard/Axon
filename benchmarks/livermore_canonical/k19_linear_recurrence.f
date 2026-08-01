C     Kernel 19 -- General Linear Recurrence Equations (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body (forward + backward sweep, both executed):
C       KB5I = 0
C       DO 191 k=1,n: B5(k+KB5I) = SA(k) + STB5*SB(k); STB5 = B5(k+KB5I) - STB5
C       DO 193 i=1,n: k=n-i+1; B5(k+KB5I) = SA(k) + STB5*SB(k); STB5 = B5(k+KB5I) - STB5
C
      PROGRAM K19
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION B5(101), SA(101), SB(101)
      DIMENSION SPACER(39)
C
C     Initialize SPACER and pull STB5 from canonical position 35
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 5 K = 1, 39
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SPACER(K) = (BUZZ - FIZZ) * 0.1D0
    5 CONTINUE
      STB5_INIT = SPACER(35)
C
C     Initialize SA using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SA(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
C     Initialize SB using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 15 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SB(K) = (BUZZ - FIZZ) * 0.1D0
   15 CONTINUE
C
C     Zero out B5
C
      DO 20 K = 1, 101
         B5(K) = 0.0D0
   20 CONTINUE
C
      N = 101
C
C     Kernel loop (canonical: forward sweep then backward sweep)
C
      DO 500 REP = 1, 39200000
         STB5 = STB5_INIT
         KB5I = 0
C        Forward sweep (DO 191)
         DO 200 K = 1, N
            B5(K+KB5I) = SA(K) + STB5*SB(K)
            STB5 = B5(K+KB5I) - STB5
  200    CONTINUE
C        Backward sweep (DO 193)
         DO 300 I = 1, N
            K = N - I + 1
            B5(K+KB5I) = SA(K) + STB5*SB(K)
            STB5 = B5(K+KB5I) - STB5
  300    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) B5(N)
  900 FORMAT('b5(n) = ', E25.15)
      END
