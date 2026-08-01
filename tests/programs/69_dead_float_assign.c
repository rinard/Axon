#include <stdio.h>
#include <stdint.h>
int main() {
    double a = 0, b = 0, c = 0, r = 0;
    a = 1.5;
    b = 2.5;
    c = 9.9;
    a = 3.0;
    r = a + b;
    printf("%s = %f\n", "a", a);
    printf("%s = %f\n", "b", b);
    printf("%s = %f\n", "c", c);
    printf("%s = %f\n", "r", r);
    return 0;
}
