      PROGRAM ARRSIEVE
      INTEGER*8 N,I,J,COUNT,LASTP
      LOGICAL T
      LOGICAL P(0:59)
      N=60
      I=0
   10 IF (I.GE.N) GOTO 20
      P(I)=.TRUE.
      I=I+1
      GOTO 10
   20 CONTINUE
      P(0)=.FALSE.
      P(1)=.FALSE.
      I=2
   30 IF (I*I.GE.N) GOTO 50
      T=P(I)
      IF (T) THEN
        J=I*I
   40   IF (J.GE.N) GOTO 45
        P(J)=.FALSE.
        J=J+I
        GOTO 40
   45   CONTINUE
      ENDIF
      I=I+1
      GOTO 30
   50 CONTINUE
      COUNT=0
      LASTP=0
      I=0
   60 IF (I.GE.N) GOTO 70
      T=P(I)
      IF (T) THEN
        COUNT=COUNT+1
        LASTP=I
      ENDIF
      I=I+1
      GOTO 60
   70 CONTINUE
      WRITE(*,'(A,I0)') 'primes=',COUNT
      WRITE(*,'(A,I0)') 'lastprime=',LASTP
      T=P(7)
      IF (T) THEN
        WRITE(*,'(A)') 'is7prime=true'
      ELSE
        WRITE(*,'(A)') 'is7prime=false'
      ENDIF
      T=P(9)
      IF (T) THEN
        WRITE(*,'(A)') 'is9prime=true'
      ELSE
        WRITE(*,'(A)') 'is9prime=false'
      ENDIF
      END
