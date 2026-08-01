#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t a=17,b=4,c=9,mn=0,mx=0,med=0,sum=0;
  if(a<b){ mn=a; } else { mn=b; }
  if(c<mn){ mn=c; } else { mn=mn; }
  if(a>b){ mx=a; } else { mx=b; }
  if(c>mx){ mx=c; } else { mx=mx; }
  sum=a+b+c;
  med=sum-mn-mx;
  printf("mn="); printf("%ld",(long)mn); printf("\n");
  printf("mx="); printf("%ld",(long)mx); printf("\n");
  printf("med="); printf("%ld",(long)med); printf("\n");
  return 0;
}
