#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,j,n,a,b,s,t;
  int64_t A[20];
  n=20;
  for(i=0;i<n;i++){ A[i]=i*i+1; }
  i=0; j=n-1;
  while(i<j){ a=A[i]; b=A[j]; A[i]=b; A[j]=a; i=i+1; j=j-1; }
  s=0;
  for(i=0;i<n;i++){ t=A[i]; s=s+t*(i+1); }
  printf("wsum="); printf("%ld",(long)s); printf("\n");
  t=A[0]; printf("first="); printf("%ld",(long)t); printf("\n");
  t=A[19]; printf("last="); printf("%ld",(long)t); printf("\n");
  return 0;
}
