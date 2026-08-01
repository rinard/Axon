#include <stdio.h>
#include <stdint.h>
int main() {
    double a = 0, b = 0, c = 0, d = 0, e = 0;
    a = 2.5;
    b = 3.5;
    c = a + b;
    d = a + b;
    e = c + d;
    printf("%s = %f\n", "a", a);
    printf("%s = %f\n", "b", b);
    printf("%s = %f\n", "c", c);
    printf("%s = %f\n", "d", d);
    printf("%s = %f\n", "e", e);
    return 0;
}
