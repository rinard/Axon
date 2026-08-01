#include <stdio.h>
int main(void){
  double f0=1.5,f1=2.5,f2=3.5,f3=4.5,f4=5.5,f5=6.5,f6=7.5,f7=8.5,f8=9.5,f9=10.5,
    f10=11.5,f11=12.5,f12=13.5,f13=14.5,f14=15.5,f15=16.5,f16=17.5,f17=18.5,f18=19.5,f19=20.5,sum;
  sum=f0+f1+f2+f3+f4+f5+f6+f7+f8+f9+f10+f11+f12+f13+f14+f15+f16+f17+f18+f19;
  sum=sum+f0*f19+f1*f18+f9*f10;
  printf("sum=%f\n",sum);
  printf("f0=%f\n",f0);
  printf("f10=%f\n",f10);
  printf("f19=%f\n",f19);
  return 0;
}
