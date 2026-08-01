      PROGRAM VALFLT
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      DIMENSION A(0:63)
      N=50
      X=1.5D0
      DO 10 I=0,N-1
        A(I)=DBLE(I)*0.5D0+1.0D0
   10 CONTINUE
      ACC=0.0D0
      DO 20 I=0,N-1
        T=A(I)*A(I)
        ACC=ACC+T
   20 CONTINUE
      ACC=SQRT(ACC)
      WRITE(*,'(A,F0.6)') 'acc=',ACC
      END
