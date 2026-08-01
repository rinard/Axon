#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a,b,c,d;
  a=1+2<<3;
  b=16+8&12;
  c=5^3|8;
  d=1<<4+1;
  printf("a="); printf("%ld",(long)a); printf("\n");
  printf("b="); printf("%ld",(long)b); printf("\n");
  printf("c="); printf("%ld",(long)c); printf("\n");
  printf("d="); printf("%ld",(long)d); printf("\n");
  return 0;
}
