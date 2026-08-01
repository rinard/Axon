#include <stdio.h>
#include <math.h>
int main(void){
  double a,b,mn,mx;
  a=3.5; b=7.25; mn=fmin(a,b); mx=fmax(a,b);
  printf("mn= %f\n",mn);
  printf("mx= %f\n",mx);
  a=-(2.0); b=-(8.0); mn=fmin(a,b); mx=fmax(a,b);
  printf("mn= %f\n",mn);
  printf("mx= %f\n",mx);
  return 0;
}
