      PROGRAM ARRFILLSUM
      INTEGER*8 I,S,T,N
      INTEGER*8 A(0:49)
      N=50
      I=0
   10 IF (I.GE.N) GOTO 20
      A(I)=I*3-7
      I=I+1
      GOTO 10
   20 CONTINUE
      S=0
      I=0
   30 IF (I.GE.N) GOTO 40
      T=A(I)
      S=S+T
      I=I+1
      GOTO 30
   40 CONTINUE
      WRITE(*,'(A,I0)') 'sum=',S
      T=A(25)
      WRITE(*,'(A,I0)') 'a25=',T
      END
