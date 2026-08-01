      PROGRAM ARRREVERSE
      INTEGER*8 I,J,N,A,B,S,T
      INTEGER*8 AR(0:19)
      N=20
      I=0
   10 IF (I.GE.N) GOTO 20
      AR(I)=I*I+1
      I=I+1
      GOTO 10
   20 CONTINUE
      I=0
      J=N-1
   30 IF (I.GE.J) GOTO 40
      A=AR(I)
      B=AR(J)
      AR(I)=B
      AR(J)=A
      I=I+1
      J=J-1
      GOTO 30
   40 CONTINUE
      S=0
      I=0
   50 IF (I.GE.N) GOTO 60
      T=AR(I)
      S=S+T*(I+1)
      I=I+1
      GOTO 50
   60 CONTINUE
      WRITE(*,'(A,I0)') 'wsum=',S
      T=AR(0)
      WRITE(*,'(A,I0)') 'first=',T
      T=AR(19)
      WRITE(*,'(A,I0)') 'last=',T
      END
