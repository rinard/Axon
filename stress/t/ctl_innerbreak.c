#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t n=0,d=0,primes=0,firstdiv=0;
  int isprime=0,found=0;
  for(n=2;n<=60;n=n+1){
    isprime=1;
    found=0;
    d=2;
    while(d<n){
      if(found){ d=n; }
      else {
        if(n%d==0){ isprime=0; found=1; firstdiv=firstdiv+d; }
        else { d=d+1; }
      }
    }
    if(isprime){ primes=primes+1; } else { primes=primes+0; }
  }
  printf("primes="); printf("%ld",(long)primes); printf("\n");
  printf("firstdiv="); printf("%ld",(long)firstdiv); printf("\n");
  return 0;
}
