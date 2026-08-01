#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=6148914691236517205LL, b=3074457345618258602LL, c,d,e,f,g;
  c=a&b; d=a|b; e=a^b; f=~a; g=~0LL;
  printf("c="); printf("%ld",(long)c); printf("\n");
  printf("d="); printf("%ld",(long)d); printf("\n");
  printf("e="); printf("%ld",(long)e); printf("\n");
  printf("f="); printf("%ld",(long)f); printf("\n");
  printf("g="); printf("%ld",(long)g); printf("\n");
  return 0;
}
