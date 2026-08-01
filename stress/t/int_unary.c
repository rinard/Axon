#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=42,b,c,d,x,cnt;
  b=-(-a);
  c=~(~a);
  d=-a-1;
  d=~a-d;
  x=-9223372036854775807LL;
  x=(int64_t)((uint64_t)x-1ULL);
  x=(int64_t)(0ULL-(uint64_t)x);
  printf("b="); printf("%ld",(long)b); printf("\n");
  printf("c="); printf("%ld",(long)c); printf("\n");
  printf("d="); printf("%ld",(long)d); printf("\n");
  printf("x="); printf("%ld",(long)x); printf("\n");
  cnt=0; a=-5;
  while(a<=5){ if(a<0){ cnt=cnt-a; } else { cnt=cnt+a; } a=a+1; }
  printf("cnt="); printf("%ld",(long)cnt); printf("\n");
  return 0;
}
