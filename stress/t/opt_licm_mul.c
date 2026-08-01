#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=7,b=13,i=0,s=0,t=0;
  for(i=0;i<1000;i=i+1){
    t=(int64_t)((uint64_t)a*(uint64_t)b);
    s=(int64_t)((uint64_t)s+(uint64_t)t+(uint64_t)i);
  }
  printf("s="); printf("%ld",(long)s); printf("\n");
  printf("t="); printf("%ld",(long)t); printf("\n");
  return 0;
}
