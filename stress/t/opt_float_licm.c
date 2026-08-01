#include <stdio.h>
#include <math.h>
int main(void){
  double a=3.0,b=1.5,s=0.0,t=0.0;
  long i;
  for(i=0;i<100;i=i+1){
    t=a*b+sqrt(a);
    s=s+t;
  }
  printf("s=%f\n",s);
  printf("t=%f\n",t);
  return 0;
}
