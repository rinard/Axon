#include <stdio.h>
#include <math.h>
int main(void){
  long i,n=20; double target=612.0,g=25.0,t;
  for(i=0;i<n;i++){ t=target/g; g=0.5*(g+t); }
  printf("g= %f\n",g);
  printf("ref= %f\n",sqrt(target));
  return 0;
}
