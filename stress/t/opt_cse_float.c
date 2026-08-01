#include <stdio.h>
int main(void){
  double x=2.5,y=4.0,z=1.5,p,q,r;
  p=(x+y)*z;
  q=(x+y)*z+x;
  r=(x+y)*z*z;
  printf("p=%f\n",p);
  printf("q=%f\n",q);
  printf("r=%f\n",r);
  return 0;
}
