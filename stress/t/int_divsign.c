#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a,b,c,d,e,f,g,h;
  a=-7/2; b=7/-2; c=-7/-2; d=7/2;
  e=-7%3; f=7%-3; g=-7%-3; h=7%3;
  printf("a="); printf("%ld",(long)a); printf("\n");
  printf("b="); printf("%ld",(long)b); printf("\n");
  printf("c="); printf("%ld",(long)c); printf("\n");
  printf("d="); printf("%ld",(long)d); printf("\n");
  printf("e="); printf("%ld",(long)e); printf("\n");
  printf("f="); printf("%ld",(long)f); printf("\n");
  printf("g="); printf("%ld",(long)g); printf("\n");
  printf("h="); printf("%ld",(long)h); printf("\n");
  return 0;
}
