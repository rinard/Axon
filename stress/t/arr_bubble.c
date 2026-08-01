#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,j,n,a,b,t,seed,ok;
  int64_t A[16];
  n=16;
  seed=12345;
  for(i=0;i<n;i++){
    seed=(int64_t)((uint64_t)seed*(uint64_t)1103515245 + (uint64_t)12345);
    t=seed%1000;
    if(t<0){ t=t+1000; }
    A[i]=t;
  }
  for(i=0;i<n-1;i++){
    for(j=0;j<n-1-i;j++){
      a=A[j]; b=A[j+1];
      if(a>b){ A[j]=b; A[j+1]=a; }
    }
  }
  ok=1;
  for(i=0;i<n-1;i++){ a=A[i]; b=A[i+1]; if(a>b){ ok=0; } }
  printf("sorted="); printf("%ld",(long)ok); printf("\n");
  t=A[0]; printf("min="); printf("%ld",(long)t); printf("\n");
  t=A[15]; printf("max="); printf("%ld",(long)t); printf("\n");
  return 0;
}
