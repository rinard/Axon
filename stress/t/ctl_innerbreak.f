      PROGRAM CTLIB
      INTEGER*8 N,D,PRIMES,FDIV
      LOGICAL ISP,FOUND
      PRIMES=0
      FDIV=0
      N=2
   10 IF (N.GT.60) GOTO 40
      ISP=.TRUE.
      FOUND=.FALSE.
      D=2
   20 IF (D.GE.N) GOTO 30
      IF (FOUND) THEN
        D=N
      ELSE
        IF (MOD(N,D).EQ.0) THEN
          ISP=.FALSE.
          FOUND=.TRUE.
          FDIV=FDIV+D
        ELSE
          D=D+1
        END IF
      END IF
      GOTO 20
   30 CONTINUE
      IF (ISP) PRIMES=PRIMES+1
      N=N+1
      GOTO 10
   40 CONTINUE
      WRITE(*,'(A,I0)') 'primes=',PRIMES
      WRITE(*,'(A,I0)') 'firstdiv=',FDIV
      END
