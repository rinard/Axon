#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t x=0,inrange=0,outside=0,i=0,cnt=0;
  for(i=0;i<30;i=i+1){
    x=i-10;
    if(x>=0 && x<=9){ inrange=1; } else { inrange=0; }
    if(x<-5 || x>15){ outside=1; } else { outside=0; }
    if(inrange==1 && outside==0){ cnt=cnt+1; } else { cnt=cnt+0; }
  }
  printf("cnt="); printf("%ld",(long)cnt); printf("\n");
  return 0;
}
