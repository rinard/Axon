#include <stdio.h>
#include <math.h>
int main(void){
  long i,n=20; double ss,norm,t,scale=1.5; double a[64];
  for(i=0;i<n;i++){ a[i]=(double)i-5.0; }
  for(i=0;i<n;i++){ a[i]=a[i]*scale; }
  ss=0.0;
  for(i=0;i<n;i++){ t=a[i]*a[i]; ss=ss+t; }
  norm=sqrt(ss);
  printf("norm= %f\n",norm);
  return 0;
}
