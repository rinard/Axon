      PROGRAM INTREASSIGN
      INTEGER*8 X,Y,I
      X=1000000007_8
      X=X+1000000007_8
      X=X*2_8
      X=X-3_8
      X=-X
      Y=9223372036854775806_8
      Y=Y+1_8
      Y=Y+1_8
      I=0
   10 IF (I.GE.50) GOTO 20
      X=X+1_8
      X=X*2_8
      X=X-I
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'x=',X
      WRITE(*,'(A,I0)') 'y=',Y
      END
