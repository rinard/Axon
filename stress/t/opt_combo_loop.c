#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=4,b=6,c=0,i=0,s=0,inv=0,t1=0,t2=0,cp=0;
  c=a+2;
  for(i=0;i<300;i=i+1){
    inv=(int64_t)((uint64_t)a*(uint64_t)b);
    cp=inv;
    t1=(int64_t)((uint64_t)(a+b)*(uint64_t)c);
    t2=(int64_t)((uint64_t)((int64_t)((uint64_t)(a+b)*(uint64_t)c))+(uint64_t)cp);
    s=(int64_t)((uint64_t)((int64_t)((uint64_t)s+(uint64_t)t1))-(uint64_t)t2+(uint64_t)i);
  }
  printf("s="); printf("%ld",(long)s); printf("\n");
  printf("inv="); printf("%ld",(long)inv); printf("\n");
  return 0;
}
