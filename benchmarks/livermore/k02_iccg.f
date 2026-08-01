C     Kernel 2 -- ICCG excerpt (Incomplete Cholesky Conjugate Gradient)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K02
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), V(1001)
      INTEGER IPNT, IPNTP, II
C
C     Initialize arrays using SIGNEL pattern
C
      SCALED = 0.1D0
C
C     Initialize V
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          V(K) = (BUZZ - FIZZ) * SCALED
   10 CONTINUE
C
      N = 101
      DO 200 REP = 1, 11495000
C         Reset X each rep
          FUZZ  = 1.2345D-3
          BUZZ  = 1.0D0 + FUZZ
          FIZZ  = 1.1D0 * FUZZ
          DO 20 K = 1, 1001
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              X(K) = (BUZZ - FIZZ) * SCALED
   20     CONTINUE
C
          II = N
          IPNTP = 0
  100     CONTINUE
              IPNT = IPNTP
              IPNTP = IPNTP + II
              II = II / 2
              I = IPNTP
              DO 90 K = IPNT + 2, IPNTP, 2
                  I = I + 1
                  X(I) = X(K) - V(K) * X(K-1) - V(K+1) * X(K+1)
   90         CONTINUE
          IF (II .GT. 0) GO TO 100
  200 CONTINUE
C
      WRITE(*,900) X(1)
  900 FORMAT('K2 ICCG: x(1) = ', E25.15)
      END
