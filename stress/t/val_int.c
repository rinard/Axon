#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n=20,s=0,i=1,p=1;
  while(i<=n){ s=s+i; p=p*i; i=i+1; }
  printf("sum="); printf("%ld",(long)s); printf("\n");
  printf("fact="); printf("%ld",(long)p); printf("\n");
  return 0;
}
