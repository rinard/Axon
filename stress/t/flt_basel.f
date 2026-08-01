      PROGRAM FBASEL
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 K,N
      N=5000
      SUM=0.0D0
      DO 10 K=1,N-1
        AKF=DBLE(K)
        D=AKF*AKF
        SUM=SUM+1.0D0/D
   10 CONTINUE
      WRITE(*,'(A,F0.6)') 'sum= ',SUM
      END
