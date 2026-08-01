      PROGRAM VALINT
      INTEGER*8 N,S,I,P
      N=20
      S=0
      I=1
      P=1
   10 IF (I.GT.N) GOTO 20
      S=S+I
      P=P*I
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'sum=',S
      WRITE(*,'(A,I0)') 'fact=',P
      END
