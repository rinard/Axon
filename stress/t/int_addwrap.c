#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=9223372036854775807LL, b, c, d;
  b=(int64_t)((uint64_t)a + 1ULL);
  c=(int64_t)((uint64_t)a + (uint64_t)a);
  d=-9223372036854775807LL;
  d=(int64_t)((uint64_t)d - 2ULL);
  printf("b="); printf("%ld",(long)b); printf("\n");
  printf("c="); printf("%ld",(long)c); printf("\n");
  printf("d="); printf("%ld",(long)d); printf("\n");
  return 0;
}
