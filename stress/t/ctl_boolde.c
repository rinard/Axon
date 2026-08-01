#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=3,b=7,c=5,r1=0,r2=0,r3=0,r4=0,li=0,ri=0;
  int p,q,lhs,rhs;
  p=(a<b);
  q=(b<c);
  lhs=!(p && q);
  rhs=(!p) || (!q);
  li = lhs ? 1 : 0;
  ri = rhs ? 1 : 0;
  r1 = (li==ri) ? 1 : 0;
  printf("dm1="); printf("%ld",(long)r1); printf("\n");
  lhs=!(p || q);
  rhs=(!p) && (!q);
  li = lhs ? 1 : 0;
  ri = rhs ? 1 : 0;
  r2 = (li==ri) ? 1 : 0;
  printf("dm2="); printf("%ld",(long)r2); printf("\n");
  r3 = (p && q) ? 1 : 0;
  r4 = (p || q) ? 1 : 0;
  printf("r3="); printf("%ld",(long)r3); printf("\n");
  printf("r4="); printf("%ld",(long)r4); printf("\n");
  r1 = (!p) ? 1 : 0;
  r2 = (!(a==b) && (c!=a)) ? 1 : 0;
  printf("r5="); printf("%ld",(long)r1); printf("\n");
  printf("r6="); printf("%ld",(long)r2); printf("\n");
  return 0;
}
