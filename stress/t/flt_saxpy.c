#include <stdio.h>
#include <math.h>
int main(void){
  long i,n=40; double a=2.5,sum,t; double x[64],y[64];
  for(i=0;i<n;i++){ x[i]=(double)i*0.25; y[i]=(double)i+1.0; }
  for(i=0;i<n;i++){ y[i]=a*x[i]+y[i]; }
  sum=0.0;
  for(i=0;i<n;i++){ t=y[i]; sum=sum+t; }
  printf("sum= %f\n",sum);
  return 0;
}
