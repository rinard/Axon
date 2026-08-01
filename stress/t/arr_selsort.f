      PROGRAM ARRSELSORT
      INTEGER*8 I,J,N,MI,MV,V,T,OK
      INTEGER*8 AR(0:13)
      N=14
      I=0
   10 IF (I.GE.N) GOTO 20
      AR(I)=MOD((N-I)*7,23_8)
      I=I+1
      GOTO 10
   20 CONTINUE
      I=0
   30 IF (I.GE.N-1) GOTO 60
      MI=I
      MV=AR(I)
      J=I+1
   40 IF (J.GE.N) GOTO 50
      V=AR(J)
      IF (V.LT.MV) THEN
        MV=V
        MI=J
      ENDIF
      J=J+1
      GOTO 40
   50 CONTINUE
      T=AR(I)
      AR(I)=MV
      AR(MI)=T
      I=I+1
      GOTO 30
   60 CONTINUE
      OK=1
      I=0
   70 IF (I.GE.N-1) GOTO 80
      V=AR(I)
      T=AR(I+1)
      IF (V.GT.T) OK=0
      I=I+1
      GOTO 70
   80 CONTINUE
      WRITE(*,'(A,I0)') 'sorted=',OK
      T=AR(0)
      WRITE(*,'(A,I0)') 'min=',T
      T=AR(13)
      WRITE(*,'(A,I0)') 'max=',T
      END
