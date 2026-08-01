#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,n,t,u,sadd,smul,scopy;
  int64_t A[30],B[30],C[30],D[30];
  n=30;
  for(i=0;i<n;i++){ A[i]=i*2+1; B[i]=i*i-5; }
  for(i=0;i<n;i++){ t=A[i]; C[i]=t; }
  for(i=0;i<n;i++){ t=A[i]; u=B[i]; D[i]=t+u; }
  scopy=0; sadd=0; smul=0;
  for(i=0;i<n;i++){
    t=C[i]; scopy=scopy+t;
    u=D[i]; sadd=sadd+u;
    t=A[i]; u=B[i]; smul=smul+t*u;
  }
  printf("copy="); printf("%ld",(long)scopy); printf("\n");
  printf("add="); printf("%ld",(long)sadd); printf("\n");
  printf("mul="); printf("%ld",(long)smul); printf("\n");
  return 0;
}
