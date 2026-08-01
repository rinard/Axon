#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, c = 0, d = 0, e = 0;
    a = 10;
    b = 3;
    c = a + b;
    d = a - b;
    e = a * b;
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "d", d);
    printf("%s = %ld\n", "e", e);
    return 0;
}
