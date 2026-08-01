#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,n,run,t,last;
  int64_t A[25],P[25];
  n=25;
  for(i=0;i<n;i++){ A[i]=(i*7+3)%17; }
  run=0;
  for(i=0;i<n;i++){ t=A[i]; run=run+t; P[i]=run; }
  t=P[0]; printf("p0="); printf("%ld",(long)t); printf("\n");
  t=P[12]; printf("p12="); printf("%ld",(long)t); printf("\n");
  last=P[24]; printf("plast="); printf("%ld",(long)last); printf("\n");
  return 0;
}
