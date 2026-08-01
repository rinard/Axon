      PROGRAM CTLACC
      INTEGER*8 I,S3,S5,SB,CE,X
      S3=0
      S5=0
      SB=0
      CE=0
      I=1
   10 IF (I.GT.100) GOTO 20
      X=I
      IF (MOD(X,3_8).EQ.0) S3=S3+X
      IF (MOD(X,5_8).EQ.0) S5=S5+X
      IF ((MOD(X,3_8).EQ.0).AND.(MOD(X,5_8).EQ.0)) SB=SB+X
      IF (MOD(X,2_8).EQ.0) CE=CE+1
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'sum3=',S3
      WRITE(*,'(A,I0)') 'sum5=',S5
      WRITE(*,'(A,I0)') 'sumboth=',SB
      WRITE(*,'(A,I0)') 'cntev=',CE
      END
