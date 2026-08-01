#include <stdio.h>
#include <stdint.h>
int main(void){
  uint64_t a=1234567ULL, c=9999ULL, e=2718281ULL;
  uint64_t b=(uint64_t)(-7654321LL), d=(uint64_t)(-333LL);
  uint64_t r;
  r = a*b + c*d - e*a + b*c - d*e + a*c - b*d;
  printf("r1="); printf("%ld",(long)(int64_t)r); printf("\n");
  r = a - b - c - d - e;
  printf("r2="); printf("%ld",(long)(int64_t)r); printf("\n");
  r = a + b*c - d + e*a - b + c*d - e + a;
  printf("r3="); printf("%ld",(long)(int64_t)r); printf("\n");
  {
    int64_t sa=1234567,sb=-7654321,sc=9999,sd=-333,se=2718281,sr;
    sr=(int64_t)(((uint64_t)(((uint64_t)(((uint64_t)((uint64_t)(sa+sb)*(uint64_t)sc)+(uint64_t)sd)*(uint64_t)se))-(uint64_t)sa)));
    sr=sr%1000000007LL;
    printf("r4="); printf("%ld",(long)sr); printf("\n");
  }
  return 0;
}
