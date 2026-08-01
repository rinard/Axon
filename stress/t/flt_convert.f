      PROGRAM FCONV
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,J
      I=7
      X=DBLE(I)+0.5D0
      WRITE(*,'(A,F0.6)') 'x= ',X
      X=3.9D0
      J=INT(X)
      WRITE(*,'(A,I0)') 'j= ',J
      X=3.1D0
      J=INT(X)
      WRITE(*,'(A,I0)') 'j= ',J
      X=-(3.9D0)
      J=INT(X)
      WRITE(*,'(A,I0)') 'j= ',J
      X=-(3.1D0)
      J=INT(X)
      WRITE(*,'(A,I0)') 'j= ',J
      X=1234.999D0
      J=INT(X)
      WRITE(*,'(A,I0)') 'j= ',J
      END
