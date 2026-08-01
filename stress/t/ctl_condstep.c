#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t i=0,s=0;
  while(i<100){
    s=s+i;
    if(i%2==0){ i=i+1; } else { i=i+3; }
  }
  printf("s="); printf("%ld",(long)s); printf("\n");
  printf("i="); printf("%ld",(long)i); printf("\n");
  return 0;
}
