#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=1071,b=462,t;
  while(b!=0){ t=a%b; a=b; b=t; }
  printf("gcd="); printf("%ld",(long)a); printf("\n");
  a=123456; b=7890;
  while(b!=0){ t=a%b; a=b; b=t; }
  printf("gcd2="); printf("%ld",(long)a); printf("\n");
  return 0;
}
