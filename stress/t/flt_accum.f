      PROGRAM FACCUM
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      N=1000
      ACC=0.0D0
      DO 10 I=1,N-1
        ACC=ACC+DBLE(I)*0.001D0
   10 CONTINUE
      WRITE(*,'(A,F0.6)') 'acc= ',ACC
      END
