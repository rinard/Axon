#include <stdio.h>
#include <math.h>
int main(void){
  double r;
  r=round(0.5); printf("r= %f\n",r);
  r=round(1.5); printf("r= %f\n",r);
  r=round(2.5); printf("r= %f\n",r);
  r=round(-(0.5)); printf("r= %f\n",r);
  r=round(-(1.5)); printf("r= %f\n",r);
  r=round(100.4999); printf("r= %f\n",r);
  r=round(-(100.5001)); printf("r= %f\n",r);
  return 0;
}
