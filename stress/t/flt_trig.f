      PROGRAM FTRIG
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      X=0.7D0
      S=SIN(X)
      C=COS(X)
      T=TAN(X)
      WRITE(*,'(A,F0.6)') 's= ',S
      WRITE(*,'(A,F0.6)') 'c= ',C
      WRITE(*,'(A,F0.6)') 't= ',T
      X=3.14159D0
      S=SIN(X)
      C=COS(X)
      WRITE(*,'(A,F0.6)') 's= ',S
      WRITE(*,'(A,F0.6)') 'c= ',C
      END
