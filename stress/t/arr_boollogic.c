#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n,i,cnt,both;
  int tb,ub,allf,anyt,alt;
  int B[24],C[24];
  n=24;
  for(i=0;i<n;i++){ B[i]=(i%2==0); C[i]=(i%3==0); }
  cnt=0;
  for(i=0;i<n;i++){ tb=B[i]; if(tb){ cnt=cnt+1; } }
  allf=1;
  for(i=0;i<n;i++){ tb=B[i]; allf=allf&&tb; }
  anyt=0;
  for(i=0;i<n;i++){ tb=C[i]; anyt=anyt||tb; }
  both=0;
  for(i=0;i<n;i++){ tb=B[i]; ub=C[i]; if(tb&&ub){ both=both+1; } }
  alt=1;
  for(i=0;i<n-1;i++){ tb=B[i]; ub=B[i+1]; if(tb==ub){ alt=0; } }
  printf("count_true_B="); printf("%ld",(long)cnt); printf("\n");
  printf("all_B="); printf("%s", allf?"true":"false"); printf("\n");
  printf("any_C="); printf("%s", anyt?"true":"false"); printf("\n");
  printf("both_BC="); printf("%ld",(long)both); printf("\n");
  printf("alternating_B="); printf("%s", alt?"true":"false"); printf("\n");
  return 0;
}
