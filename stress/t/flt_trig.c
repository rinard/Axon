#include <stdio.h>
#include <math.h>
int main(void){
  double x,s,c,t;
  x=0.7; s=sin(x); c=cos(x); t=tan(x);
  printf("s= %f\n",s);
  printf("c= %f\n",c);
  printf("t= %f\n",t);
  x=3.14159; s=sin(x); c=cos(x);
  printf("s= %f\n",s);
  printf("c= %f\n",c);
  return 0;
}
