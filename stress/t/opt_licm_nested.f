      PROGRAM OLICMN
      INTEGER*8 A,B,C,I,J,S,INV,T
      A=3
      B=5
      C=11
      S=0
      I=0
   10 IF (I.GE.50) GOTO 40
      INV=A*B-C
      J=0
   20 IF (J.GE.20) GOTO 30
      T=INV*2+A*C
      S=S+T+I-J
      J=J+1
      GOTO 20
   30 CONTINUE
      I=I+1
      GOTO 10
   40 CONTINUE
      WRITE(*,'(A,I0)') 's=',S
      END
