      PROGRAM ARRHIST
      INTEGER*8 I,N,K,V,IDX,T,TOTAL,MX
      INTEGER*8 A(0:39),H(0:6)
      N=40
      K=7
      I=0
   10 IF (I.GE.K) GOTO 20
      H(I)=0
      I=I+1
      GOTO 10
   20 CONTINUE
      I=0
   30 IF (I.GE.N) GOTO 40
      A(I)=I*I*3+11
      I=I+1
      GOTO 30
   40 CONTINUE
      I=0
   50 IF (I.GE.N) GOTO 60
      V=A(I)
      IDX=MOD(V,K)
      T=H(IDX)
      H(IDX)=T+1
      I=I+1
      GOTO 50
   60 CONTINUE
      TOTAL=0
      MX=0
      I=0
   70 IF (I.GE.K) GOTO 80
      T=H(I)
      TOTAL=TOTAL+T
      IF (T.GT.MX) MX=T
      WRITE(*,'(A,I0,A,I0)') 'h',I,'=',T
      I=I+1
      GOTO 70
   80 CONTINUE
      WRITE(*,'(A,I0)') 'total=',TOTAL
      WRITE(*,'(A,I0)') 'maxbin=',MX
      END
