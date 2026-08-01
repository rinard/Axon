      PROGRAM FPOWABS
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      A=2.0D0
      B=10.0D0
      P=A**B
      WRITE(*,'(A,F0.6)') 'p= ',P
      A=3.0D0
      B=0.5D0
      P=A**B
      WRITE(*,'(A,F0.6)') 'p= ',P
      AN=-(5.25D0)
      WRITE(*,'(A,F0.6)') 'n= ',AN
      AN=ABS(-(7.5D0))
      WRITE(*,'(A,F0.6)') 'abs= ',AN
      R=ANINT(2.4D0)
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(2.6D0)
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(-(2.6D0))
      WRITE(*,'(A,F0.6)') 'r= ',R
      END
