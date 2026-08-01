#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i=0,sum=0,val=0,lastidx=0;
  int done=0;
  for(i=0;i<50;i=i+1){
    if(done){ sum=sum+0; }
    else {
      val=i*i-30;
      if(val>100){ done=1; lastidx=i; }
      else { sum=sum+val; }
    }
  }
  printf("sum="); printf("%ld",(long)sum); printf("\n");
  printf("lastidx="); printf("%ld",(long)lastidx); printf("\n");
  return 0;
}
