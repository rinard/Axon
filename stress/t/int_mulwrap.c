#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=3037000500LL, b, c, e;
  b=(int64_t)((uint64_t)a * (uint64_t)a);
  c=9223372036854775807LL;
  c=(int64_t)((uint64_t)c * 3ULL);
  e=(int64_t)(-9223372036854775807LL - 1LL);
  e=(int64_t)((uint64_t)e * (uint64_t)e);
  printf("b="); printf("%ld",(long)b); printf("\n");
  printf("c="); printf("%ld",(long)c); printf("\n");
  printf("e="); printf("%ld",(long)e); printf("\n");
  return 0;
}
