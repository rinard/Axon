#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t x=17,y=23,z=4,p,q,r;
  p=(int64_t)((uint64_t)(x+y)*(uint64_t)z);
  q=(int64_t)((uint64_t)((int64_t)((uint64_t)(x+y)*(uint64_t)z))+1ULL);
  r=(int64_t)((uint64_t)((int64_t)((uint64_t)(x+y)*(uint64_t)z))-(uint64_t)(x+y));
  printf("p="); printf("%ld",(long)p); printf("\n");
  printf("q="); printf("%ld",(long)q); printf("\n");
  printf("r="); printf("%ld",(long)r); printf("\n");
  return 0;
}
