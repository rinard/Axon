      PROGRAM INTSUMSQ
      INTEGER*8 S,I,N,IALT
      S=0
      I=1
      N=1000
   10 IF (I.GT.N) GOTO 20
      S=S+I*I
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'sumsq=',S
      IALT=0
      I=1
   30 IF (I.GT.N) GOTO 40
      IALT=IALT+(-1_8)*I
      S=S-I
      I=I+1
      GOTO 30
   40 CONTINUE
      WRITE(*,'(A,I0)') 'alt=',IALT
      END
