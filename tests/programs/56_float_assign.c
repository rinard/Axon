#include <stdio.h>
#include <stdint.h>
int main() {
    double x = 0, y = 0;
    int64_t n = 0;
    x = 3.0;
    y = 7.5;
    n = 42;
    printf("%s = %f\n", "x", x);
    printf("%s = %f\n", "y", y);
    printf("%s = %ld\n", "n", n);
    return 0;
}
