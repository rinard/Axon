#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t w,h,r,c,acc,t,s,mx;
  int64_t G[35],O[35];
  w=7; h=5;
  for(r=0;r<h;r++){ for(c=0;c<w;c++){ G[r*w+c]=(r*w+c)%9; } }
  for(r=0;r<h;r++){
    for(c=0;c<w;c++){
      acc=0;
      t=G[r*w+c]; acc=acc+t;
      if(r>0){ t=G[(r-1)*w+c]; acc=acc+t; }
      if(r<h-1){ t=G[(r+1)*w+c]; acc=acc+t; }
      if(c>0){ t=G[r*w+(c-1)]; acc=acc+t; }
      if(c<w-1){ t=G[r*w+(c+1)]; acc=acc+t; }
      O[r*w+c]=acc;
    }
  }
  s=0; mx=0;
  for(r=0;r<h*w;r++){ t=O[r]; s=s+t; if(t>mx){ mx=t; } }
  printf("stencil_sum="); printf("%ld",(long)s); printf("\n");
  printf("stencil_max="); printf("%ld",(long)mx); printf("\n");
  t=O[2*w+3]; printf("center="); printf("%ld",(long)t); printf("\n");
  t=O[0]; printf("corner="); printf("%ld",(long)t); printf("\n");
  return 0;
}
