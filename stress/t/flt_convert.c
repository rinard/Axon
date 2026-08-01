#include <stdio.h>
#include <math.h>
int main(void){
  long i,j; double x;
  i=7; x=(double)i+0.5;
  printf("x= %f\n",x);
  x=3.9; j=(long)x;
  printf("j= %ld\n",j);
  x=3.1; j=(long)x;
  printf("j= %ld\n",j);
  x=-(3.9); j=(long)x;
  printf("j= %ld\n",j);
  x=-(3.1); j=(long)x;
  printf("j= %ld\n",j);
  x=1234.999; j=(long)x;
  printf("j= %ld\n",j);
  return 0;
}
