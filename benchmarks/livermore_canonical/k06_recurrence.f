C     Kernel 6 -- General linear recurrence equations (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: DO i=2,n: W(i)=0.01; DO k=1,i-1: W(i)=W(i)+B(i,k)*W(i-k)
C     B is column-major (i fast, k slow); flat index (k-1)*64 + i.
C
      PROGRAM K06
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION W(64), B(64,64)
C
C     Initialize B array using SIGNEL pattern (column-major: i fast, k slow)
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 15 K = 1, 64
          DO 10 I = 1, 64
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              B(I,K) = (BUZZ - FIZZ) * 0.1D0
   10     CONTINUE
   15 CONTINUE
C
      N = 64
      DO 200 REP = 1, 10000000
C         Reset W each rep
          DO 20 J = 1, 64
              W(J) = 0.0D0
   20     CONTINUE
          W(1) = 0.01D0
C
C         Kernel loop
C
          DO 100 I = 2, N
              W(I) = 0.01D0
              DO 90 K = 1, I-1
                  W(I) = W(I) + B(I,K) * W(I-K)
   90         CONTINUE
  100     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) W(64)
  900 FORMAT('w(64) = ', E25.15)
      END
