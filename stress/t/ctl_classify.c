#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t x=0,i=0,negc=0,zero=0,pos=0,big=0;
  for(i=0;i<20;i=i+1){
    x=(i*7)%11-5;
    if(x<0){ negc=negc+1; }
    else { if(x==0){ zero=zero+1; } else { if(x>3){ big=big+1; } else { pos=pos+1; } } }
  }
  printf("negc="); printf("%ld",(long)negc); printf("\n");
  printf("zero="); printf("%ld",(long)zero); printf("\n");
  printf("pos="); printf("%ld",(long)pos); printf("\n");
  printf("big="); printf("%ld",(long)big); printf("\n");
  return 0;
}
