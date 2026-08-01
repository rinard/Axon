#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i,n,k,v,idx,t,total,mx;
  int64_t A[40],H[7];
  n=40; k=7;
  for(i=0;i<k;i++){ H[i]=0; }
  for(i=0;i<n;i++){ A[i]=i*i*3+11; }
  for(i=0;i<n;i++){ v=A[i]; idx=v%k; t=H[idx]; H[idx]=t+1; }
  total=0; mx=0;
  for(i=0;i<k;i++){
    t=H[i]; total=total+t;
    if(t>mx){ mx=t; }
    printf("h"); printf("%ld",(long)i); printf("="); printf("%ld",(long)t); printf("\n");
  }
  printf("total="); printf("%ld",(long)total); printf("\n");
  printf("maxbin="); printf("%ld",(long)mx); printf("\n");
  return 0;
}
