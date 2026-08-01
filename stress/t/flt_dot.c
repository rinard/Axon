#include <stdio.h>
#include <math.h>
int main(void){
  long i,n=32; double dot,p; double u[64],v[64];
  for(i=0;i<n;i++){ u[i]=(double)i*0.5-1.0; v[i]=(double)i*0.1+2.0; }
  dot=0.0;
  for(i=0;i<n;i++){ p=u[i]*v[i]; dot=dot+p; }
  printf("dot= %f\n",dot);
  return 0;
}
