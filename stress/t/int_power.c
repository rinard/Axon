#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t base=3,ex=40,r=1,i=0;
  while(i<ex){ r=(int64_t)((uint64_t)r*(uint64_t)base); i=i+1; }
  printf("p1="); printf("%ld",(long)r); printf("\n");
  base=7; ex=25; r=1; i=0;
  while(i<ex){ r=(int64_t)((uint64_t)r*(uint64_t)base); i=i+1; }
  printf("p2="); printf("%ld",(long)r); printf("\n");
  return 0;
}
