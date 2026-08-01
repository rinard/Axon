      PROGRAM INTUNARY
      INTEGER*8 A,B,C,D,X,CNT
      A=42
      B=-(-A)
      C=NOT(NOT(A))
      D=-A-1
      D=NOT(A)-D
      X=-9223372036854775807_8
      X=X-1_8
      X=-X
      WRITE(*,'(A,I0)') 'b=',B
      WRITE(*,'(A,I0)') 'c=',C
      WRITE(*,'(A,I0)') 'd=',D
      WRITE(*,'(A,I0)') 'x=',X
      CNT=0
      A=-5
   10 IF (A.GT.5) GOTO 20
      IF (A.LT.0) THEN
        CNT=CNT-A
      ELSE
        CNT=CNT+A
      END IF
      A=A+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'cnt=',CNT
      END
