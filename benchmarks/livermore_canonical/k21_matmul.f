C     Kernel 21 -- Matrix*Matrix Product (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body:
C       DO 21 k=1,25; DO 21 i=1,25; DO 21 j=1,n:
C         PX(i,j) = PX(i,j) + VY(i,k) * CX(k,j)
C
      PROGRAM K21
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION PX(25,101), VY(101,25), CX(25,101)
C
C     Initialize PX to zero
C
      DO 6 J = 1, 101
         DO 5 I = 1, 25
            PX(I,J) = 0.0D0
    5    CONTINUE
    6 CONTINUE
C
C     Initialize VY using SIGNEL (column-major fill: outer K=1..25, inner I=1..101)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 K = 1, 25
         DO 11 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VY(I,K) = (BUZZ - FIZZ) * 0.1D0
   11    CONTINUE
   12 CONTINUE
C
C     Initialize CX using SIGNEL (column-major fill: outer J=1..101, inner K=1..25)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 101
         DO 13 K = 1, 25
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            CX(K,J) = (BUZZ - FIZZ) * 0.1D0
   13    CONTINUE
   14 CONTINUE
C
      N = 101
C
C     Kernel loop (canonical: PX(i,j) += VY(i,k) * CX(k,j))
C
      DO 500 REP = 1, 425000
         DO 300 K = 1, 25
            DO 200 I = 1, 25
               DO 100 J = 1, N
                  PX(I,J) = PX(I,J) + VY(I,K) * CX(K,J)
  100          CONTINUE
  200       CONTINUE
  300    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) PX(1,1)
  900 FORMAT('px(1,1) = ', E25.15)
      END
