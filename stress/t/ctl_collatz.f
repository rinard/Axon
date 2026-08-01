      PROGRAM CTLCOLL
      INTEGER*8 START,N,STEPS,TOT,MAXS,MAXST
      TOT=0
      MAXS=0
      MAXST=0
      START=1
   10 IF (START.GT.27) GOTO 40
      N=START
      STEPS=0
   20 IF ((N.EQ.1).OR.(STEPS.GE.1000)) GOTO 30
      IF (MOD(N,2_8).EQ.0) THEN
        N=N/2
      ELSE
        N=3*N+1
      END IF
      STEPS=STEPS+1
      GOTO 20
   30 CONTINUE
      TOT=TOT+STEPS
      IF (STEPS.GT.MAXS) THEN
        MAXS=STEPS
        MAXST=START
      END IF
      START=START+1
      GOTO 10
   40 CONTINUE
      WRITE(*,'(A,I0)') 'totsteps=',TOT
      WRITE(*,'(A,I0)') 'maxsteps=',MAXS
      WRITE(*,'(A,I0)') 'maxstart=',MAXST
      END
