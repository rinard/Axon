#include <stdio.h>
#include <math.h>
int main(void){
  long i,n=5; double x=1.7,acc,c; double coef[8];
  coef[0]=1.0; coef[1]=-(3.0); coef[2]=2.0; coef[3]=0.5; coef[4]=-(1.25);
  acc=0.0;
  for(i=n-1;i>=0;i--){ c=coef[i]; acc=acc*x+c; }
  printf("p= %f\n",acc);
  return 0;
}
