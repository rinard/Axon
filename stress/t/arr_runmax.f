      PROGRAM ARRRUNMAX
      INTEGER*8 I,N,M,MI,T,CHK
      INTEGER*8 A(0:19),R(0:19)
      N=20
      I=0
   10 IF (I.GE.N) GOTO 20
      A(I)=MOD(I*13+5,29_8)-10
      I=I+1
      GOTO 10
   20 CONTINUE
      M=A(0)
      I=0
   30 IF (I.GE.N) GOTO 40
      T=A(I)
      IF (T.GT.M) M=T
      R(I)=M
      I=I+1
      GOTO 30
   40 CONTINUE
      M=A(0)
      MI=0
      I=1
   50 IF (I.GE.N) GOTO 60
      T=A(I)
      IF (T.GT.M) THEN
        M=T
        MI=I
      ENDIF
      I=I+1
      GOTO 50
   60 CONTINUE
      CHK=R(19)
      WRITE(*,'(A,I0)') 'runmax_last=',CHK
      CHK=R(10)
      WRITE(*,'(A,I0)') 'runmax10=',CHK
      WRITE(*,'(A,I0)') 'maxval=',M
      WRITE(*,'(A,I0)') 'maxidx=',MI
      END
