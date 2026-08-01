#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=99,b,c,d,e,r;
  b=a;
  c=b;
  d=c;
  e=d+a;
  r=a+b+c+d+e;
  printf("r="); printf("%ld",(long)r); printf("\n");
  printf("e="); printf("%ld",(long)e); printf("\n");
  return 0;
}
