#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a0=1,a1=1,a2=2,a3=3,a4=5,a5=8,a6=13,a7=21,a8=34,a9=55,
    a10=2,a11=4,a12=6,a13=8,a14=10,a15=12,a16=14,a17=16,a18=18,a19=20,
    a20=3,a21=6,a22=9,a23=12,a24=15,a25=18,a26=21,a27=24,a28=27,a29=30,
    a30=5,a31=10,a32=15,a33=20,a34=25,a35=30,a36=35,a37=40,a38=45,a39=50,
    acc=0,i=0;
  for(i=0;i<7;i=i+1){
    acc=acc+a0+a39+a1+a38+a2+a37+a3+a36+a4+a35;
    acc=acc+a5+a34+a6+a33+a7+a32+a8+a31+a9+a30;
    acc=acc+a10+a29+a11+a28+a12+a27+a13+a26+a14+a25;
    acc=acc+a15+a24+a16+a23+a17+a22+a18+a21+a19+a20;
    acc=(int64_t)((uint64_t)acc+(uint64_t)((int64_t)((uint64_t)i*(uint64_t)a0))+(uint64_t)((int64_t)((uint64_t)a20*(uint64_t)a21)));
  }
  printf("acc="); printf("%ld",(long)acc); printf("\n");
  printf("a0="); printf("%ld",(long)a0); printf("\n");
  printf("a20="); printf("%ld",(long)a20); printf("\n");
  printf("a39="); printf("%ld",(long)a39); printf("\n");
  return 0;
}
