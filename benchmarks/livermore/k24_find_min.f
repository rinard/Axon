C     Kernel 24 -- Find Location of First Minimum in Array
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K24
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION X(1001)
C
C     Initialize X using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 10 K = 1, 1001
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         X(K) = (BUZZ - FIZZ) * SCALED
   10 CONTINUE
C
      N = 1001
C
C     Kernel 24: Find Location of First Minimum
C
      DO 500 IREP = 1, 30595000
         X(N/2+1) = -1.0D+10
         M = 1
         DO 200 K = 2, N
            IF (X(K) .LT. X(M)) M = K
  200    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) M, X(M)
  900 FORMAT('K24 find min: m = ', I6, ', x(m) = ', E23.15E3)
      END
