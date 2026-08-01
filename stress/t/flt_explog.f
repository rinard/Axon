      PROGRAM FEXPLOG
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      X=2.5D0
      E=EXP(X)
      AL=LOG(X)
      WRITE(*,'(A,F0.6)') 'e= ',E
      WRITE(*,'(A,F0.6)') 'l= ',AL
      X=8.0D0
      AL2=LOG(X)/LOG(2.0D0)
      WRITE(*,'(A,F0.6)') 'l2= ',AL2
      X=1000.0D0
      AL10=LOG10(X)
      WRITE(*,'(A,F0.6)') 'l10= ',AL10
      END
