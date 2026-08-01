#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, y = 0, r = 0;
    double a = 0, b = 0;
    x = 42;
    a = 1.0;
    y = 10;
    b = 2.0;
    x = 7;
    a = 3.5;
    r = x + y;
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "y", y);
    printf("%s = %f\n", "a", a);
    printf("%s = %f\n", "b", b);
    printf("%s = %ld\n", "r", r);
    return 0;
}
