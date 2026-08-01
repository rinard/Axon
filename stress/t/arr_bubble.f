      PROGRAM ARRBUBBLE
      INTEGER*8 I,J,N,A,B,T,SEED,OK,C1
      INTEGER*8 AR(0:15)
      N=16
      SEED=12345
      C1=1103515245
      I=0
   10 IF (I.GE.N) GOTO 20
      SEED=SEED*C1+12345
      T=MOD(SEED,1000_8)
      IF (T.LT.0) T=T+1000
      AR(I)=T
      I=I+1
      GOTO 10
   20 CONTINUE
      I=0
   30 IF (I.GE.N-1) GOTO 60
      J=0
   40 IF (J.GE.N-1-I) GOTO 50
      A=AR(J)
      B=AR(J+1)
      IF (A.GT.B) THEN
        AR(J)=B
        AR(J+1)=A
      ENDIF
      J=J+1
      GOTO 40
   50 CONTINUE
      I=I+1
      GOTO 30
   60 CONTINUE
      OK=1
      I=0
   70 IF (I.GE.N-1) GOTO 80
      A=AR(I)
      B=AR(I+1)
      IF (A.GT.B) OK=0
      I=I+1
      GOTO 70
   80 CONTINUE
      WRITE(*,'(A,I0)') 'sorted=',OK
      T=AR(0)
      WRITE(*,'(A,I0)') 'min=',T
      T=AR(15)
      WRITE(*,'(A,I0)') 'max=',T
      END
