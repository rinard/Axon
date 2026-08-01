#include <stdio.h>
#include <math.h>
int main(void){
  long i=5,j=2; double x,y;
  x=(double)(i/j);
  printf("x= %f\n",x);
  y=(double)i+0.5;
  printf("y= %f\n",y);
  y=3.0*(double)i-(double)j;
  printf("y= %f\n",y);
  x=1.0/(double)i;
  printf("x= %f\n",x);
  y=(double)(i*j)+0.25*(double)i;
  printf("y= %f\n",y);
  return 0;
}
