#include <stdio.h>
#include <math.h>
int main(void){
  double x,y,d,a,b,r;
  x=3.0; y=4.0; d=sqrt(x*x+y*y);
  printf("d= %f\n",d);
  a=exp(log(7.5));
  printf("a= %f\n",a);
  b=pow(2.0,0.5)*pow(2.0,0.5);
  printf("b= %f\n",b);
  r=fmax(sin(1.0),cos(1.0));
  printf("r= %f\n",r);
  r=fabs(-(sqrt(2.0)));
  printf("r= %f\n",r);
  return 0;
}
