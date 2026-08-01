      PROGRAM CTLCOND
      INTEGER*8 I,S
      S=0
      I=0
   10 IF (I.GE.100) GOTO 20
      S=S+I
      IF (MOD(I,2_8).EQ.0) THEN
        I=I+1
      ELSE
        I=I+3
      END IF
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 's=',S
      WRITE(*,'(A,I0)') 'i=',I
      END
