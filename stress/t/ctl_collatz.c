#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t start=0,n=0,steps=0,totsteps=0,maxsteps=0,maxstart=0;
  for(start=1;start<=27;start=start+1){
    n=start;
    steps=0;
    while(n!=1 && steps<1000){
      if(n%2==0){ n=n/2; } else { n=3*n+1; }
      steps=steps+1;
    }
    totsteps=totsteps+steps;
    if(steps>maxsteps){ maxsteps=steps; maxstart=start; } else { maxsteps=maxsteps; }
  }
  printf("totsteps="); printf("%ld",(long)totsteps); printf("\n");
  printf("maxsteps="); printf("%ld",(long)maxsteps); printf("\n");
  printf("maxstart="); printf("%ld",(long)maxstart); printf("\n");
  return 0;
}
