#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, c = 0, d = 0, e = 0, r = 0;
    a = 3;
    b = 7;
    c = a + b;
    d = c * a;
    e = d - b;
    r = e + c;
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "d", d);
    printf("%s = %ld\n", "e", e);
    printf("%s = %ld\n", "r", r);
    return 0;
}
