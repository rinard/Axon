#include <stdio.h>
#include <math.h>
int main(void){
  double x,y;
  x=2.0; y=sqrt(x);
  printf("y= %f\n",y);
  x=1000000.0; y=sqrt(x);
  printf("y= %f\n",y);
  return 0;
}
