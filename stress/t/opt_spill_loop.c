#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t b0=1,b1=2,b2=3,b3=4,b4=5,b5=6,b6=7,b7=8,b8=9,b9=10,b10=11,b11=12,
    b12=13,b13=14,b14=15,b15=16,b16=17,b17=18,b18=19,b19=20,b20=21,b21=22,b22=23,b23=24,
    i=0,acc=0;
  for(i=0;i<50;i=i+1){
    acc=acc+b0+b1+b2+b3+b4+b5+b6+b7+b8+b9+b10+b11;
    acc=acc+b12+b13+b14+b15+b16+b17+b18+b19+b20+b21+b22+b23;
    acc=(int64_t)((uint64_t)acc+(uint64_t)i+(uint64_t)((int64_t)((uint64_t)b0*(uint64_t)b23)));
  }
  printf("acc="); printf("%ld",(long)acc); printf("\n");
  printf("b0="); printf("%ld",(long)b0); printf("\n");
  printf("b23="); printf("%ld",(long)b23); printf("\n");
  return 0;
}
