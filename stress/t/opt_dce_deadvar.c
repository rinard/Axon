#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=10,b=20,c=30,used=0,i=0;
  for(i=0;i<100;i=i+1){
    a=a+1;
    b=(int64_t)((uint64_t)b*2ULL);
    c=c-3;
    used=used+i;
  }
  printf("used="); printf("%ld",(long)used); printf("\n");
  return 0;
}
