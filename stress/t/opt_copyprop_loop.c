#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=0,b=0,c=0,d=0,i=0,s=0;
  for(i=0;i<150;i=i+1){
    a=i+1;
    b=a;
    c=b;
    d=c+b;
    s=s+a+b+c+d;
  }
  printf("s="); printf("%ld",(long)s); printf("\n");
  return 0;
}
