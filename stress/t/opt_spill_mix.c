#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i0=1,i1=2,i2=3,i3=4,i4=5,i5=6,i6=7,i7=8,i8=9,i9=10,i10=11,i11=12,i12=13,i13=14,i14=15,i15=16,isum;
  double g0=1.25,g1=2.25,g2=3.25,g3=4.25,g4=5.25,g5=6.25,g6=7.25,g7=8.25,g8=9.25,g9=10.25,g10=11.25,g11=12.25,g12=13.25,g13=14.25,g14=15.25,g15=16.25,fsum;
  isum=i0+i1+i2+i3+i4+i5+i6+i7+i8+i9+i10+i11+i12+i13+i14+i15;
  fsum=g0+g1+g2+g3+g4+g5+g6+g7+g8+g9+g10+g11+g12+g13+g14+g15;
  isum=(int64_t)((uint64_t)isum+(uint64_t)((int64_t)((uint64_t)i0*(uint64_t)i15))+(uint64_t)((int64_t)((uint64_t)i7*(uint64_t)i8)));
  fsum=fsum+g0*g15+g7*g8;
  printf("isum="); printf("%ld",(long)isum); printf("\n");
  printf("fsum=%f\n",fsum);
  printf("i0="); printf("%ld",(long)i0); printf("\n");
  printf("g15=%f\n",g15);
  return 0;
}
