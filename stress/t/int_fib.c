#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=0,b=1,t,i=0,n=90;
  while(i<n){ t=(int64_t)((uint64_t)a+(uint64_t)b); a=b; b=t; i=i+1; }
  printf("fib90="); printf("%ld",(long)a); printf("\n");
  printf("fib91="); printf("%ld",(long)b); printf("\n");
  return 0;
}
