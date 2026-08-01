#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,n,m,mi,t,chk;
  int64_t A[20],R[20];
  n=20;
  for(i=0;i<n;i++){ A[i]=(i*13+5)%29-10; }
  m=A[0];
  for(i=0;i<n;i++){ t=A[i]; if(t>m){ m=t; } R[i]=m; }
  m=A[0]; mi=0;
  for(i=1;i<n;i++){ t=A[i]; if(t>m){ m=t; mi=i; } }
  chk=R[19]; printf("runmax_last="); printf("%ld",(long)chk); printf("\n");
  chk=R[10]; printf("runmax10="); printf("%ld",(long)chk); printf("\n");
  printf("maxval="); printf("%ld",(long)m); printf("\n");
  printf("maxidx="); printf("%ld",(long)mi); printf("\n");
  return 0;
}
