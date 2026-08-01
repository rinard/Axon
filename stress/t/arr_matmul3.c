#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n,r,c,k,acc,a,b,t,s;
  int64_t A[9],B[9],C[9];
  n=3;
  for(r=0;r<n;r++){
    for(c=0;c<n;c++){
      A[r*n+c]=r*n+c+1;
      if(r==c){ B[r*n+c]=1; } else { B[r*n+c]=0; }
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
  for(r=0;r<n;r++){ for(c=0;c<n;c++){ t=C[r*n+c]; s=s+t; } }
  printf("trace_sum="); printf("%ld",(long)s); printf("\n");
  t=C[4]; printf("c11="); printf("%ld",(long)t); printf("\n");
  return 0;
}
