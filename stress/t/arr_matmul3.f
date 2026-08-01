      PROGRAM ARRMATMUL3
      INTEGER*8 N,R,C,K,ACC,A,B,T,S
      INTEGER*8 AR(0:8),BR(0:8),CR(0:8)
      N=3
      R=0
   10 IF (R.GE.N) GOTO 30
      C=0
   20 IF (C.GE.N) GOTO 25
      AR(R*N+C)=R*N+C+1
      IF (R.EQ.C) THEN
        BR(R*N+C)=1
      ELSE
        BR(R*N+C)=0
      ENDIF
      C=C+1
      GOTO 20
   25 CONTINUE
      R=R+1
      GOTO 10
   30 CONTINUE
      R=0
   40 IF (R.GE.N) GOTO 70
      C=0
   50 IF (C.GE.N) GOTO 65
      ACC=0
      K=0
   55 IF (K.GE.N) GOTO 60
      A=AR(R*N+K)
      B=BR(K*N+C)
      ACC=ACC+A*B
      K=K+1
      GOTO 55
   60 CONTINUE
      CR(R*N+C)=ACC
      C=C+1
      GOTO 50
   65 CONTINUE
      R=R+1
      GOTO 40
   70 CONTINUE
      S=0
      R=0
   80 IF (R.GE.N) GOTO 100
      C=0
   90 IF (C.GE.N) GOTO 95
      T=CR(R*N+C)
      S=S+T
      C=C+1
      GOTO 90
   95 CONTINUE
      R=R+1
      GOTO 80
  100 CONTINUE
      WRITE(*,'(A,I0)') 'trace_sum=',S
      T=CR(4)
      WRITE(*,'(A,I0)') 'c11=',T
      END
