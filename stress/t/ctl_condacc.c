#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i=0,sum3=0,sum5=0,sumboth=0,cntev=0,x=0;
  for(i=1;i<=100;i=i+1){
    x=i;
    if(x%3==0){ sum3=sum3+x; } else { sum3=sum3+0; }
    if(x%5==0){ sum5=sum5+x; } else { sum5=sum5+0; }
    if(x%3==0 && x%5==0){ sumboth=sumboth+x; } else { sumboth=sumboth+0; }
    if(x%2==0){ cntev=cntev+1; } else { cntev=cntev+0; }
  }
  printf("sum3="); printf("%ld",(long)sum3); printf("\n");
  printf("sum5="); printf("%ld",(long)sum5); printf("\n");
  printf("sumboth="); printf("%ld",(long)sumboth); printf("\n");
  printf("cntev="); printf("%ld",(long)cntev); printf("\n");
  return 0;
}
