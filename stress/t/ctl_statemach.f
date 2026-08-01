      PROGRAM CTLSM
      INTEGER*8 STATE,I,SYM,ACC,STEPS
      STATE=0
      ACC=0
      STEPS=0
      I=0
   10 IF (I.GE.40) GOTO 20
      SYM=MOD(I*3+1,3_8)
      IF (STATE.EQ.0) THEN
        IF (SYM.EQ.0) THEN
          STATE=1
        ELSE
          STATE=0
        END IF
      ELSE IF (STATE.EQ.1) THEN
        IF (SYM.EQ.1) THEN
          STATE=2
        ELSE
          STATE=0
        END IF
      ELSE IF (STATE.EQ.2) THEN
        IF (SYM.EQ.2) THEN
          STATE=0
          ACC=ACC+1
        ELSE
          STATE=1
        END IF
      ELSE
        STATE=0
      END IF
      STEPS=STEPS+1
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'accepts=',ACC
      WRITE(*,'(A,I0)') 'state=',STATE
      END
