      PROGRAM FROUND
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      R=ANINT(0.5D0)
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(1.5D0)
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(2.5D0)
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(-(0.5D0))
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(-(1.5D0))
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(100.4999D0)
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ANINT(-(100.5001D0))
      WRITE(*,'(A,F0.6)') 'r= ',R
      END
