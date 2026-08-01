#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,j,n,mi,mv,v,t,ok;
  int64_t A[14];
  n=14;
  for(i=0;i<n;i++){ A[i]=(n-i)*7%23; }
  for(i=0;i<n-1;i++){
    mi=i; mv=A[i];
    for(j=i+1;j<n;j++){ v=A[j]; if(v<mv){ mv=v; mi=j; } }
    t=A[i]; A[i]=mv; A[mi]=t;
  }
  ok=1;
  for(i=0;i<n-1;i++){ v=A[i]; t=A[i+1]; if(v>t){ ok=0; } }
  printf("sorted="); printf("%ld",(long)ok); printf("\n");
  t=A[0]; printf("min="); printf("%ld",(long)t); printf("\n");
  t=A[13]; printf("max="); printf("%ld",(long)t); printf("\n");
  return 0;
}
