#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t n = 0, i = 0;
    double x = 0, total = 0;
    n = 10;
    total = 0.0;
    i = 1;
    while (i <= n) {
        x = (double)i;
        total = total + x * x;
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %f\n", "x", x);
    printf("%s = %f\n", "total", total);
    printf("%s = %ld\n", "i", i);
    return 0;
}
