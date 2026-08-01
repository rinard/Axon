      PROGRAM CTLPAR
      INTEGER*8 V,T,BITS,PAR,ODDP,I
      ODDP=0
      I=0
   10 IF (I.GE.64) GOTO 40
      V=I*2654435761_8
      V=IAND(V,1023_8)
      T=V
      BITS=0
   20 IF (T.EQ.0) GOTO 30
      IF (IAND(T,1_8).EQ.1) BITS=BITS+1
      T=ISHFT(T,-1)
      GOTO 20
   30 CONTINUE
      PAR=MOD(BITS,2_8)
      IF (PAR.EQ.1) ODDP=ODDP+1
      I=I+1
      GOTO 10
   40 CONTINUE
      WRITE(*,'(A,I0)') 'oddpar=',ODDP
      END
