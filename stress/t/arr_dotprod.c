#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,n,a,b,dot,t;
  int64_t U[32],W[32];
  n=32;
  for(i=0;i<n;i++){ U[i]=i-16; W[i]=2*i+3; }
  dot=0;
  for(i=0;i<n;i++){ a=U[i]; b=W[i]; dot=dot+a*b; }
  printf("dot="); printf("%ld",(long)dot); printf("\n");
  t=U[31]; printf("u31="); printf("%ld",(long)t); printf("\n");
  t=W[0]; printf("w0="); printf("%ld",(long)t); printf("\n");
  return 0;
}
