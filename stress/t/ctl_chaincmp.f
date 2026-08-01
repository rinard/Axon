      PROGRAM CTLCHAIN
      INTEGER*8 X,INR,OUT,I,CNT
      CNT=0
      I=0
   10 IF (I.GE.30) GOTO 20
      X=I-10
      IF ((X.GE.0).AND.(X.LE.9)) THEN
        INR=1
      ELSE
        INR=0
      END IF
      IF ((X.LT.-5).OR.(X.GT.15)) THEN
        OUT=1
      ELSE
        OUT=0
      END IF
      IF ((INR.EQ.1).AND.(OUT.EQ.0)) THEN
        CNT=CNT+1
      ELSE
        CNT=CNT+0
      END IF
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'cnt=',CNT
      END
