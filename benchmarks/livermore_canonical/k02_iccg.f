C     Kernel 2 -- ICCG excerpt (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K02
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(2050), V(2050)
      INTEGER IPNT, IPNTP, II
C
C     Initialize V using SIGNEL pattern
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 2050
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          V(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
      N = 1001
      DO 200 REP = 1, 7500000
C         Reset X each rep
          FUZZ  = 1.2345D-3
          BUZZ  = 1.0D0 + FUZZ
          FIZZ  = 1.1D0 * FUZZ
          DO 20 K = 1, 2050
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              X(K) = (BUZZ - FIZZ) * 0.1D0
   20     CONTINUE
C
          II = N
          IPNTP = 0
  222     CONTINUE
              IPNT = IPNTP
              IPNTP = IPNTP + II
              II = II / 2
              I = IPNTP + 1
              DO 90 K = IPNT + 2, IPNTP, 2
                  I = I + 1
                  X(I) = X(K) - V(K) * X(K-1) - V(K+1) * X(K+1)
   90         CONTINUE
          IF (II .GT. 1) GO TO 222
  200 CONTINUE
C
      WRITE(*,900) X(N)
  900 FORMAT('x(n) = ', E25.15)
      END
