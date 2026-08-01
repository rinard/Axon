#include <stdio.h>
#include <stdint.h>
int main() {
    double a = 0, b = 0, s = 0, d = 0, p = 0, q = 0;
    a = 10.0;
    b = 3.0;
    s = a + b;
    d = a - b;
    p = a * b;
    q = a / b;
    printf("%s = %f\n", "a", a);
    printf("%s = %f\n", "b", b);
    printf("%s = %f\n", "s", s);
    printf("%s = %f\n", "d", d);
    printf("%s = %f\n", "p", p);
    printf("%s = %f\n", "q", q);
    return 0;
}
