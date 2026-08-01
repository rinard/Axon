#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t state=0,i=0,sym=0,accepts=0,steps=0;
  for(i=0;i<40;i=i+1){
    sym=(i*3+1)%3;
    if(state==0){ if(sym==0){ state=1; } else { state=0; } }
    else { if(state==1){ if(sym==1){ state=2; } else { state=0; } }
      else { if(state==2){ if(sym==2){ state=0; accepts=accepts+1; } else { state=1; } }
        else { state=0; } } }
    steps=steps+1;
  }
  printf("accepts="); printf("%ld",(long)accepts); printf("\n");
  printf("state="); printf("%ld",(long)state); printf("\n");
  return 0;
}
