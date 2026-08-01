#include <stdio.h>
#include <math.h>
int main(void){
  long i,n=50; double acc,x=1.5,t; double a[64];
  for(i=0;i<n;i++){ a[i]=(double)i*0.5+1.0; }
  acc=0.0;
  for(i=0;i<n;i++){ t=a[i]*a[i]; acc=acc+t; }
  acc=sqrt(acc);
  printf("acc=%f\n",acc);
  return 0;
}
