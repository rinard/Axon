#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n=10,m,i=0,s=0;
  m=n*2;
  for(i=0;i<m;i=i+1){
    s=(int64_t)((uint64_t)s+(uint64_t)((int64_t)((uint64_t)i*(uint64_t)n)));
  }
  printf("m="); printf("%ld",(long)m); printf("\n");
  printf("s="); printf("%ld",(long)s); printf("\n");
  return 0;
}
