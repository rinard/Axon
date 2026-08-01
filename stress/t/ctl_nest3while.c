#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i=0,j=0,k=0,s=0;
  for(i=0;i<5;i=i+1){
    for(j=0;j<4;j=j+1){
      for(k=0;k<3;k=k+1){
        s=s+i*100+j*10+k;
      }
    }
  }
  printf("s="); printf("%ld",(long)s); printf("\n");
  return 0;
}
