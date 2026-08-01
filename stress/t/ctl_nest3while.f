      PROGRAM CTLN3
      INTEGER*8 I,J,K,S
      S=0
      I=0
   10 IF (I.GE.5) GOTO 60
      J=0
   20 IF (J.GE.4) GOTO 50
      K=0
   30 IF (K.GE.3) GOTO 40
      S=S+I*100+J*10+K
      K=K+1
      GOTO 30
   40 CONTINUE
      J=J+1
      GOTO 20
   50 CONTINUE
      I=I+1
      GOTO 10
   60 CONTINUE
      WRITE(*,'(A,I0)') 's=',S
      END
