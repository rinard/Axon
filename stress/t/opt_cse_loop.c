#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=6,b=9,i=0,s=0,u=0,v=0;
  for(i=0;i<200;i=i+1){
    u=(int64_t)((uint64_t)(a+i)*(uint64_t)(b+i));
    v=(int64_t)((uint64_t)((int64_t)((uint64_t)(a+i)*(uint64_t)(b+i)))+(uint64_t)a);
    s=(int64_t)((uint64_t)((int64_t)((uint64_t)s+(uint64_t)u))-(uint64_t)v);
  }
  printf("s="); printf("%ld",(long)s); printf("\n");
  return 0;
}
