#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a=0,b=0,c=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0;
    int64_t l=0,m=0,n=0,p=0,q=0,s=0,t=0,u=0,v=0,w=0;
    int64_t r=0,i=0;
    a=1;b=2;c=3;d=4;e=5;f=6;g=7;h=8;j=9;k=10;
    l=11;m=12;n=13;p=14;q=15;s=16;t=17;u=18;v=19;w=20;
    i=0;
    while (i < 2) {
        r = a+b;
        r = r+c;
        r = r+d;
        r = r+e;
        r = r+f;
        r = r+g;
        r = r+h;
        r = r+j;
        r = r+k;
        r = r+l;
        r = r+m;
        r = r+n;
        r = r+p;
        r = r+q;
        r = r+s;
        r = r+t;
        r = r+u;
        r = r+v;
        r = r+w;
        a++;b++;c++;d++;e++;f++;g++;h++;j++;k++;
        l++;m++;n++;p++;q++;s++;t++;u++;v++;w++;
        i++;
    }
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "d", d);
    printf("%s = %ld\n", "e", e);
    printf("%s = %ld\n", "f", f);
    printf("%s = %ld\n", "g", g);
    printf("%s = %ld\n", "h", h);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "k", k);
    printf("%s = %ld\n", "l", l);
    printf("%s = %ld\n", "m", m);
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "p", p);
    printf("%s = %ld\n", "q", q);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "t", t);
    printf("%s = %ld\n", "u", u);
    printf("%s = %ld\n", "v", v);
    printf("%s = %ld\n", "w", w);
    printf("%s = %ld\n", "r", r);
    printf("%s = %ld\n", "i", i);
    return 0;
}
