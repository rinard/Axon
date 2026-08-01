#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n,r,c,acc,a,x,t,s;
  int64_t M[36],V[6],Y[6];
  n=6;
  for(r=0;r<n;r++){
    V[r]=r+1;
    for(c=0;c<n;c++){ M[r*n+c]=(r+1)*(c+1)-r; }
  }
  for(r=0;r<n;r++){
    acc=0;
    for(c=0;c<n;c++){ a=M[r*n+c]; x=V[c]; acc=acc+a*x; }
    Y[r]=acc;
  }
  s=0;
  for(r=0;r<n;r++){ t=Y[r]; s=s+t; }
  printf("ysum="); printf("%ld",(long)s); printf("\n");
  t=Y[0]; printf("y0="); printf("%ld",(long)t); printf("\n");
  t=Y[5]; printf("y5="); printf("%ld",(long)t); printf("\n");
  return 0;
}
