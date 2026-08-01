C     Kernel 19 -- General Linear Recurrence Equations
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K19
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION B5(1001), SA(1001), SB(1001)
C
C     Initialize SA using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 10 K = 1, 101
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SA(K) = (BUZZ - FIZZ) * SCALED
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
         SB(K) = (BUZZ - FIZZ) * SCALED
   15 CONTINUE
C
C     Zero out B5
C
      DO 20 K = 1, 1001
         B5(K) = 0.0D0
   20 CONTINUE
C
      N = 101
C
C     Kernel 19: General Linear Recurrence Equations
C     Forward and backward sweeps with recurrence
C
      DO 500 IREP = 1, 30088000
         STB5 = 0.5D0
         KB5I = 0
C
C        Forward sweep
         DO 200 K = 1, N
            B5(K+KB5I) = SA(K) + STB5*SB(K)
            STB5 = B5(K+KB5I) - STB5
  200    CONTINUE
C
C        Backward sweep
         DO 300 I = 1, N
            K = N - I + 1
            B5(K+KB5I) = SA(K) + STB5*SB(K)
            STB5 = B5(K+KB5I) - STB5
  300    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) B5(51)
  900 FORMAT('K19 linear recurrence: b5(51) = ', E23.15E3)
      END
