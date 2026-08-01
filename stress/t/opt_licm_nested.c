#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=3,b=5,c=11,i=0,j=0,s=0,inv=0,t=0;
  for(i=0;i<50;i=i+1){
    inv=(int64_t)((uint64_t)((int64_t)((uint64_t)a*(uint64_t)b))-(uint64_t)c);
    for(j=0;j<20;j=j+1){
      t=(int64_t)((uint64_t)((int64_t)((uint64_t)inv*2ULL))+(uint64_t)((int64_t)((uint64_t)a*(uint64_t)c)));
      s=(int64_t)((uint64_t)((int64_t)((uint64_t)s+(uint64_t)t+(uint64_t)i))-(uint64_t)j);
    }
  }
  printf("s="); printf("%ld",(long)s); printf("\n");
  return 0;
}
