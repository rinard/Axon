      PROGRAM OFLICM
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I
      A=3.0D0
      B=1.5D0
      S=0.0D0
      I=0
   10 IF (I.GE.100) GOTO 20
      T=A*B+SQRT(A)
      S=S+T
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,F0.6)') 's=',S
      WRITE(*,'(A,F0.6)') 't=',T
      END
