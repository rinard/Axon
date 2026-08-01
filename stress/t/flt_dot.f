      PROGRAM FDOT
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      DIMENSION U(0:63),V(0:63)
      N=32
      DO 10 I=0,N-1
        U(I)=DBLE(I)*0.5D0-1.0D0
        V(I)=DBLE(I)*0.1D0+2.0D0
   10 CONTINUE
      DOT=0.0D0
      DO 20 I=0,N-1
        P=U(I)*V(I)
        DOT=DOT+P
   20 CONTINUE
      WRITE(*,'(A,F0.6)') 'dot= ',DOT
      END
