      PROGRAM ARRPREFIX
      INTEGER*8 I,N,RUN,T,LAST
      INTEGER*8 A(0:24),P(0:24)
      N=25
      I=0
   10 IF (I.GE.N) GOTO 20
      A(I)=MOD(I*7+3,17_8)
      I=I+1
      GOTO 10
   20 CONTINUE
      RUN=0
      I=0
   30 IF (I.GE.N) GOTO 40
      T=A(I)
      RUN=RUN+T
      P(I)=RUN
      I=I+1
      GOTO 30
   40 CONTINUE
      T=P(0)
      WRITE(*,'(A,I0)') 'p0=',T
      T=P(12)
      WRITE(*,'(A,I0)') 'p12=',T
      LAST=P(24)
      WRITE(*,'(A,I0)') 'plast=',LAST
      END
