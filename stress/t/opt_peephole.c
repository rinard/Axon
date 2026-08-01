#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t x=41,a,b,c,d,e;
  a=x+0;
  b=(int64_t)((uint64_t)a*1ULL);
  c=b-0;
  d=(int64_t)((uint64_t)c*2ULL);
  e=(int64_t)((uint64_t)d+(uint64_t)((int64_t)((uint64_t)d*0ULL)));
  e=(int64_t)((uint64_t)((int64_t)((uint64_t)((int64_t)((uint64_t)e+(uint64_t)(x&x)))-(uint64_t)(x|x)))+(uint64_t)(x^0));
  printf("a="); printf("%ld",(long)a); printf("\n");
  printf("d="); printf("%ld",(long)d); printf("\n");
  printf("e="); printf("%ld",(long)e); printf("\n");
  return 0;
}
