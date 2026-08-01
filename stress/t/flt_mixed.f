      PROGRAM FMIXED
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,J
      I=5
      J=2
      X=DBLE(I/J)
      WRITE(*,'(A,F0.6)') 'x= ',X
      Y=DBLE(I)+0.5D0
      WRITE(*,'(A,F0.6)') 'y= ',Y
      Y=3.0D0*DBLE(I)-DBLE(J)
      WRITE(*,'(A,F0.6)') 'y= ',Y
      X=1.0D0/DBLE(I)
      WRITE(*,'(A,F0.6)') 'x= ',X
      Y=DBLE(I*J)+0.25D0*DBLE(I)
      WRITE(*,'(A,F0.6)') 'y= ',Y
      END
