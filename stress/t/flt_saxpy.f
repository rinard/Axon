      PROGRAM FSAXPY
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      DIMENSION X(0:63),Y(0:63)
      N=40
      A=2.5D0
      DO 10 I=0,N-1
        X(I)=DBLE(I)*0.25D0
        Y(I)=DBLE(I)+1.0D0
   10 CONTINUE
      DO 20 I=0,N-1
        Y(I)=A*X(I)+Y(I)
   20 CONTINUE
      SUM=0.0D0
      DO 30 I=0,N-1
        T=Y(I)
        SUM=SUM+T
   30 CONTINUE
      WRITE(*,'(A,F0.6)') 'sum= ',SUM
      END
