      PROGRAM CTLBOOLDE
      INTEGER*8 A,B,C,R1,R2,R3,R4,LI,RI
      LOGICAL P,Q,LHS,RHS
      A=3
      B=7
      C=5
      P = (A.LT.B)
      Q = (B.LT.C)
      LHS = .NOT.(P.AND.Q)
      RHS = (.NOT.P).OR.(.NOT.Q)
      IF (LHS) THEN
        LI=1
      ELSE
        LI=0
      END IF
      IF (RHS) THEN
        RI=1
      ELSE
        RI=0
      END IF
      IF (LI.EQ.RI) THEN
        R1=1
      ELSE
        R1=0
      END IF
      WRITE(*,'(A,I0)') 'dm1=',R1
      LHS = .NOT.(P.OR.Q)
      RHS = (.NOT.P).AND.(.NOT.Q)
      IF (LHS) THEN
        LI=1
      ELSE
        LI=0
      END IF
      IF (RHS) THEN
        RI=1
      ELSE
        RI=0
      END IF
      IF (LI.EQ.RI) THEN
        R2=1
      ELSE
        R2=0
      END IF
      WRITE(*,'(A,I0)') 'dm2=',R2
      IF (P.AND.Q) THEN
        R3=1
      ELSE
        R3=0
      END IF
      IF (P.OR.Q) THEN
        R4=1
      ELSE
        R4=0
      END IF
      WRITE(*,'(A,I0)') 'r3=',R3
      WRITE(*,'(A,I0)') 'r4=',R4
      IF (.NOT.P) THEN
        R1=1
      ELSE
        R1=0
      END IF
      IF ((.NOT.(A.EQ.B)).AND.(C.NE.A)) THEN
        R2=1
      ELSE
        R2=0
      END IF
      WRITE(*,'(A,I0)') 'r5=',R1
      WRITE(*,'(A,I0)') 'r6=',R2
      END
