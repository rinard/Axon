      PROGRAM CTLCLASS
      INTEGER*8 X,I,NEG,ZERO,POS,BIG
      NEG=0
      ZERO=0
      POS=0
      BIG=0
      I=0
   10 IF (I.GE.20) GOTO 20
      X=MOD(I*7,11_8)-5
      IF (X.LT.0) THEN
        NEG=NEG+1
      ELSE IF (X.EQ.0) THEN
        ZERO=ZERO+1
      ELSE IF (X.GT.3) THEN
        BIG=BIG+1
      ELSE
        POS=POS+1
      END IF
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'negc=',NEG
      WRITE(*,'(A,I0)') 'zero=',ZERO
      WRITE(*,'(A,I0)') 'pos=',POS
      WRITE(*,'(A,I0)') 'big=',BIG
      END
