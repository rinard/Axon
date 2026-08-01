#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i=0,c=0,n=0;
  i=5; while(i<5){ c=c+1; i=i+1; }
  i=0; while(i>10){ c=c+100; i=i+1; }
  i=0; while(i<n){ c=c+1000; i=i+1; }
  printf("c="); printf("%ld",(long)c); printf("\n");
  return 0;
}
