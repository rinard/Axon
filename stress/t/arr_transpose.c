#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t rows,cols,r,c,t,s,ok,a,b;
  int64_t M[24],T[24];
  rows=4; cols=6;
  for(r=0;r<rows;r++){ for(c=0;c<cols;c++){ M[r*cols+c]=r*10+c; } }
  for(r=0;r<rows;r++){ for(c=0;c<cols;c++){ t=M[r*cols+c]; T[c*rows+r]=t; } }
  ok=1;
  for(r=0;r<rows;r++){ for(c=0;c<cols;c++){
    a=M[r*cols+c]; b=T[c*rows+r];
    if(a==b){ } else { ok=0; }
  } }
  s=0;
  for(r=0;r<cols*rows;r++){ t=T[r]; s=s+t; }
  printf("ok="); printf("%ld",(long)ok); printf("\n");
  printf("tsum="); printf("%ld",(long)s); printf("\n");
  t=T[1*rows+0]; printf("t10="); printf("%ld",(long)t); printf("\n");
  return 0;
}
