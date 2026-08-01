#include <stdio.h>
#include <math.h>
int main(void){
  long k,n=5000; double sum=0.0,d,kf;
  for(k=1;k<n;k++){ kf=(double)k; d=kf*kf; sum=sum+1.0/d; }
  printf("sum= %f\n",sum);
  return 0;
}
