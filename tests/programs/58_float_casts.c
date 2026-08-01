#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t n = 0, m = 0;
    double x = 0;
    n = 42;
    x = (double)n;
    m = (int64_t)x;
    printf("%s = %ld\n", "n", n);
    printf("%s = %f\n", "x", x);
    printf("%s = %ld\n", "m", m);
    return 0;
}
