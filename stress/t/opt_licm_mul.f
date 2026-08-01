      PROGRAM OLICMM
      INTEGER*8 A,B,I,S,T
      A=7
      B=13
      S=0
      I=0
   10 IF (I.GE.1000) GOTO 20
      T=A*B
      S=S+T+I
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 's=',S
      WRITE(*,'(A,I0)') 't=',T
      END
