#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t x,y,i;
  x=1000000007LL;
  x=(int64_t)((uint64_t)x+1000000007ULL);
  x=(int64_t)((uint64_t)x*2ULL);
  x=(int64_t)((uint64_t)x-3ULL);
  x=(int64_t)(0ULL-(uint64_t)x);
  y=9223372036854775806LL;
  y=(int64_t)((uint64_t)y+1ULL);
  y=(int64_t)((uint64_t)y+1ULL);
  i=0;
  while(i<50){
    x=(int64_t)((uint64_t)x+1ULL);
    x=(int64_t)((uint64_t)x*2ULL);
    x=(int64_t)((uint64_t)x-(uint64_t)i);
    i=i+1;
  }
  printf("x="); printf("%ld",(long)x); printf("\n");
  printf("y="); printf("%ld",(long)y); printf("\n");
  return 0;
}
