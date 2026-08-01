      PROGRAM FMINMAX
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      A=3.5D0
      B=7.25D0
      AMN=MIN(A,B)
      AMX=MAX(A,B)
      WRITE(*,'(A,F0.6)') 'mn= ',AMN
      WRITE(*,'(A,F0.6)') 'mx= ',AMX
      A=-(2.0D0)
      B=-(8.0D0)
      AMN=MIN(A,B)
      AMX=MAX(A,B)
      WRITE(*,'(A,F0.6)') 'mn= ',AMN
      WRITE(*,'(A,F0.6)') 'mx= ',AMX
      END
