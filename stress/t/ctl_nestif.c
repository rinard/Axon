#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t x=37,r=0;
  if(x<10){ r=1; } else { if(x<20){ r=2; } else { if(x<30){ r=3; } else { if(x<40){ r=4; } else { if(x<50){ r=5; } else { r=6; } } } } }
  printf("r="); printf("%ld",(long)r); printf("\n");
  return 0;
}
