#include <stdio.h>
#include <math.h>
int main(void){
  long i,n=1000; double acc=0.0;
  for(i=1;i<n;i++){ acc=acc+(double)i*0.001; }
  printf("acc= %f\n",acc);
  return 0;
}
