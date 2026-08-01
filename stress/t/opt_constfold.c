#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=5,b,c,d,e,f;
  b=a+3;
  c=b*2;
  d=c-a;
  e=(a+b+c+d)*2;
  f=e%7+(c<<1)-(d>>1);
  printf("a="); printf("%ld",(long)a); printf("\n");
  printf("e="); printf("%ld",(long)e); printf("\n");
  printf("f="); printf("%ld",(long)f); printf("\n");
  return 0;
}
