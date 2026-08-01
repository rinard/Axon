#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a,b,c,d,e,f,g;
  a=(int64_t)((uint64_t)1ULL << 10);
  b=(int64_t)((uint64_t)1ULL << 62);
  c=(int64_t)((uint64_t)(-1LL) << 4);
  d=((int64_t)-1024) >> 3;
  e=((int64_t)1024) >> 3;
  f=(int64_t)(-9223372036854775807LL - 1LL);
  f=f >> 60;
  g=((int64_t)255) >> 0;
  printf("a="); printf("%ld",(long)a); printf("\n");
  printf("b="); printf("%ld",(long)b); printf("\n");
  printf("c="); printf("%ld",(long)c); printf("\n");
  printf("d="); printf("%ld",(long)d); printf("\n");
  printf("e="); printf("%ld",(long)e); printf("\n");
  printf("f="); printf("%ld",(long)f); printf("\n");
  printf("g="); printf("%ld",(long)g); printf("\n");
  return 0;
}
