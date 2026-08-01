      PROGRAM ARRBOOLLOGIC
      INTEGER*8 N,I,CNT,BOTH
      LOGICAL TB,UB,ALLF,ANYT,ALT
      LOGICAL B(0:23),C(0:23)
      N=24
      I=0
   10 IF (I.GE.N) GOTO 20
      B(I)=(MOD(I,2_8).EQ.0)
      C(I)=(MOD(I,3_8).EQ.0)
      I=I+1
      GOTO 10
   20 CONTINUE
      CNT=0
      I=0
   30 IF (I.GE.N) GOTO 40
      TB=B(I)
      IF (TB) CNT=CNT+1
      I=I+1
      GOTO 30
   40 CONTINUE
      ALLF=.TRUE.
      I=0
   50 IF (I.GE.N) GOTO 60
      TB=B(I)
      ALLF=ALLF.AND.TB
      I=I+1
      GOTO 50
   60 CONTINUE
      ANYT=.FALSE.
      I=0
   70 IF (I.GE.N) GOTO 80
      TB=C(I)
      ANYT=ANYT.OR.TB
      I=I+1
      GOTO 70
   80 CONTINUE
      BOTH=0
      I=0
   90 IF (I.GE.N) GOTO 100
      TB=B(I)
      UB=C(I)
      IF (TB.AND.UB) BOTH=BOTH+1
      I=I+1
      GOTO 90
  100 CONTINUE
      ALT=.TRUE.
      I=0
  110 IF (I.GE.N-1) GOTO 120
      TB=B(I)
      UB=B(I+1)
      IF (TB.EQV.UB) ALT=.FALSE.
      I=I+1
      GOTO 110
  120 CONTINUE
      WRITE(*,'(A,I0)') 'count_true_B=',CNT
      IF (ALLF) THEN
        WRITE(*,'(A)') 'all_B=true'
      ELSE
        WRITE(*,'(A)') 'all_B=false'
      ENDIF
      IF (ANYT) THEN
        WRITE(*,'(A)') 'any_C=true'
      ELSE
        WRITE(*,'(A)') 'any_C=false'
      ENDIF
      WRITE(*,'(A,I0)') 'both_BC=',BOTH
      IF (ALT) THEN
        WRITE(*,'(A)') 'alternating_B=true'
      ELSE
        WRITE(*,'(A)') 'alternating_B=false'
      ENDIF
      END
