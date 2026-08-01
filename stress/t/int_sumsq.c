#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t s=0,i=1,n=1000,alt=0;
  while(i<=n){ s=s+i*i; i=i+1; }
  printf("sumsq="); printf("%ld",(long)s); printf("\n");
  alt=0; i=1;
  while(i<=n){ alt=alt+(-1)*i; s=s-i; i=i+1; }
  printf("alt="); printf("%ld",(long)alt); printf("\n");
  return 0;
}
