      PROGRAM ARRCOPYEW
      INTEGER*8 I,N,T,U,SADD,SMUL,SCOPY
      INTEGER*8 A(0:29),B(0:29),C(0:29),D(0:29)
      N=30
      I=0
   10 IF (I.GE.N) GOTO 20
      A(I)=I*2+1
      B(I)=I*I-5
      I=I+1
      GOTO 10
   20 CONTINUE
      I=0
   30 IF (I.GE.N) GOTO 40
      T=A(I)
      C(I)=T
      I=I+1
      GOTO 30
   40 CONTINUE
      I=0
   50 IF (I.GE.N) GOTO 60
      T=A(I)
      U=B(I)
      D(I)=T+U
      I=I+1
      GOTO 50
   60 CONTINUE
      SCOPY=0
      SADD=0
      SMUL=0
      I=0
   70 IF (I.GE.N) GOTO 80
      T=C(I)
      SCOPY=SCOPY+T
      U=D(I)
      SADD=SADD+U
      T=A(I)
      U=B(I)
      SMUL=SMUL+T*U
      I=I+1
      GOTO 70
   80 CONTINUE
      WRITE(*,'(A,I0)') 'copy=',SCOPY
      WRITE(*,'(A,I0)') 'add=',SADD
      WRITE(*,'(A,I0)') 'mul=',SMUL
      END
