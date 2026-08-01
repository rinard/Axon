#include <stdio.h>
#include <stdint.h>
int main(void){
  int64_t v0=1,v1=2,v2=3,v3=4,v4=5,v5=6,v6=7,v7=8,v8=9,v9=10,
    v10=11,v11=12,v12=13,v13=14,v14=15,v15=16,v16=17,v17=18,v18=19,v19=20,
    v20=21,v21=22,v22=23,v23=24,v24=25,v25=26,v26=27,v27=28,v28=29,v29=30,s;
  s=v0+v1+v2+v3+v4+v5+v6+v7+v8+v9+v10+v11+v12+v13+v14+v15+v16+v17+v18+v19+v20+v21+v22+v23+v24+v25+v26+v27+v28+v29;
  s=(int64_t)((uint64_t)s
    +(uint64_t)((int64_t)((uint64_t)v0*(uint64_t)v29))
    +(uint64_t)((int64_t)((uint64_t)v1*(uint64_t)v28))
    +(uint64_t)((int64_t)((uint64_t)v2*(uint64_t)v27))
    +(uint64_t)((int64_t)((uint64_t)v14*(uint64_t)v15)));
  printf("s="); printf("%ld",(long)s); printf("\n");
  printf("v0="); printf("%ld",(long)v0); printf("\n");
  printf("v15="); printf("%ld",(long)v15); printf("\n");
  printf("v29="); printf("%ld",(long)v29); printf("\n");
  return 0;
}
