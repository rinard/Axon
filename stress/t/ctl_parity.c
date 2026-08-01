#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t v=0,t=0,bits=0,par=0,oddpar=0,i=0;
  for(i=0;i<64;i=i+1){
    v=(int64_t)((uint64_t)i*(uint64_t)2654435761ULL);
    v=v&1023;
    t=v;
    bits=0;
    while(t!=0){
      if((t&1)==1){ bits=bits+1; } else { bits=bits+0; }
      t=t>>1;
    }
    par=bits%2;
    if(par==1){ oddpar=oddpar+1; } else { oddpar=oddpar+0; }
  }
  printf("oddpar="); printf("%ld",(long)oddpar); printf("\n");
  return 0;
}
