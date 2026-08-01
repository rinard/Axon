#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0;
    double y = 0, h = 0, z = 0, w = 0;
    x = 10;
    y = (double)x;
    h = 1.5;
    z = y + h;
    w = y + h;
    printf("%s = %ld\n", "x", x);
    printf("%s = %f\n", "y", y);
    printf("%s = %f\n", "h", h);
    printf("%s = %f\n", "z", z);
    printf("%s = %f\n", "w", w);
    return 0;
}
