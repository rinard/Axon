#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,s,t,n;
  int64_t A[50];
  n=50;
  for(i=0;i<n;i++){ A[i]=i*3-7; }
  s=0;
  for(i=0;i<n;i++){ t=A[i]; s=s+t; }
  printf("sum="); printf("%ld",(long)s); printf("\n");
  t=A[25];
  printf("a25="); printf("%ld",(long)t); printf("\n");
  return 0;
}
