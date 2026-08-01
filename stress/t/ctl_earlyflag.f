      PROGRAM CTLEARLY
      INTEGER*8 I,SUM,VAL,LASTIDX
      LOGICAL DONE
      SUM=0
      DONE=.FALSE.
      LASTIDX=0
      I=0
   10 IF (I.GE.50) GOTO 20
      IF (DONE) THEN
        SUM=SUM+0
      ELSE
        VAL=I*I-30
        IF (VAL.GT.100) THEN
          DONE=.TRUE.
          LASTIDX=I
        ELSE
          SUM=SUM+VAL
        END IF
      END IF
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'sum=',SUM
      WRITE(*,'(A,I0)') 'lastidx=',LASTIDX
      END
