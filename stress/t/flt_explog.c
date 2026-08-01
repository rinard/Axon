#include <stdio.h>
#include <math.h>
int main(void){
  double x,e,l,l2,l10;
  x=2.5; e=exp(x); l=log(x);
  printf("e= %f\n",e);
  printf("l= %f\n",l);
  x=8.0; l2=log2(x);
  printf("l2= %f\n",l2);
  x=1000.0; l10=log10(x);
  printf("l10= %f\n",l10);
  return 0;
}
