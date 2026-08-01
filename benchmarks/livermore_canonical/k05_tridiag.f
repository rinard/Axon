C     Kernel 5 -- Tri-diagonal elimination, below diagonal (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: DO i=2,n: X(i) = Z(i)*(Y(i) - X(i-1))
C
      PROGRAM K05
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION X(1001), Y(1001), Z(1001)
C
C     Initialize Y
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Y(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
C     Initialize Z
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 15 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Z(K) = (BUZZ - FIZZ) * 0.1D0
   15 CONTINUE
C
      N = 1001
      DO 200 REP = 1, 9700000
C         Reset X each rep
          FUZZ  = 1.2345D-3
          BUZZ  = 1.0D0 + FUZZ
          FIZZ  = 1.1D0 * FUZZ
          DO 20 K = 1, 1001
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              X(K) = (BUZZ - FIZZ) * 0.1D0
   20     CONTINUE
C
C         Kernel loop
C
          DO 90 I = 2, N
              X(I) = Z(I) * (Y(I) - X(I-1))
   90     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) X(N)
  900 FORMAT('x(n) = ', E25.15)
      END
