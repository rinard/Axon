C     Kernel 6 -- General linear recurrence equations
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K06
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION W(1001), B(64,64)
C
C     Initialize B array using SIGNEL pattern
C
      SCALED = 0.1D0
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 15 J = 1, 64
          DO 10 I = 1, 64
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              B(I,J) = (BUZZ - FIZZ) * SCALED
   10     CONTINUE
   15 CONTINUE
C
      N = 64
      DO 200 REP = 1, 2781000
C         Reset W each rep
          DO 20 J = 1, 1001
              W(J) = 0.0D0
   20     CONTINUE
          W(1) = 0.01D0
C
C         Kernel loop
C
          DO 100 I = 2, N
              DO 90 K = 1, I-1
                  W(I) = W(I) + B(K,I) * W(I-K)
   90         CONTINUE
  100     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) W(64)
  900 FORMAT('K6 recurrence: w(64) = ', E25.15)
      END
