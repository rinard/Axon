#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=5,b=3,c=7,r,s,t;
  r=(a+b)*(c-a)-b*c+(a*b*c)/2;
  s=((a-b)*c+(a+c)*b)*(c-b)-a;
  t=a+b*c-(a-b)*(c+a)/b+c%a;
  printf("r="); printf("%ld",(long)r); printf("\n");
  printf("s="); printf("%ld",(long)s); printf("\n");
  printf("t="); printf("%ld",(long)t); printf("\n");
  return 0;
}
