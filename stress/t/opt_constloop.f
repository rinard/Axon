      PROGRAM OCLOOP
      INTEGER*8 N,M,I,S
      N=10
      M=N*2
      S=0
      I=0
   10 IF (I.GE.M) GOTO 20
      S=S+I*N
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'm=',M
      WRITE(*,'(A,I0)') 's=',S
      END
