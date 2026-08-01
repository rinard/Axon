#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n,i,j,count,lastp;
  int t;
  int P[60];
  n=60;
  for(i=0;i<n;i++){ P[i]=1; }
  P[0]=0; P[1]=0;
  for(i=2;i*i<n;i++){
    t=P[i];
    if(t){ for(j=i*i;j<n;j+=i){ P[j]=0; } }
  }
  count=0; lastp=0;
  for(i=0;i<n;i++){ t=P[i]; if(t){ count=count+1; lastp=i; } }
  printf("primes="); printf("%ld",(long)count); printf("\n");
  printf("lastprime="); printf("%ld",(long)lastp); printf("\n");
  t=P[7]; printf("is7prime="); printf("%s", t?"true":"false"); printf("\n");
  t=P[9]; printf("is9prime="); printf("%s", t?"true":"false"); printf("\n");
  return 0;
}
