#include <stdio.h>
#include <math.h>
int main(void){
  double a,b,p,n,r;
  a=2.0; b=10.0; p=pow(a,b);
  printf("p= %f\n",p);
  a=3.0; b=0.5; p=pow(a,b);
  printf("p= %f\n",p);
  n=-(5.25);
  printf("n= %f\n",n);
  n=fabs(-(7.5));
  printf("abs= %f\n",n);
  r=round(2.4);
  printf("r= %f\n",r);
  r=round(2.6);
  printf("r= %f\n",r);
  r=round(-(2.6));
  printf("r= %f\n",r);
  return 0;
}
