#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n,r,c,k,acc,a,b,t,s;
  int64_t A[64],B[64],C[64];
  n=8;
  for(r=0;r<n;r++){
    for(c=0;c<n;c++){
      A[r*n+c]=(r+1)*(c+2)%13;
      B[r*n+c]=(r*3+c+1)%11;
    }
  }
  for(r=0;r<n;r++){
    for(c=0;c<n;c++){
      acc=0;
      for(k=0;k<n;k++){ a=A[r*n+k]; b=B[k*n+c]; acc=acc+a*b; }
      C[r*n+c]=acc;
    }
  }
  s=0;
  for(r=0;r<n;r++){ t=C[r*n+r]; s=s+t; }
  printf("diag="); printf("%ld",(long)s); printf("\n");
  t=C[0]; printf("c00="); printf("%ld",(long)t); printf("\n");
  t=C[63]; printf("c77="); printf("%ld",(long)t); printf("\n");
  return 0;
}
