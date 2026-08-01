#include <stdio.h>
#include <stdint.h>
int main() {
    double a = 0, b = 0;
    int64_t r = 0;
    a = 3.5;
    b = 7.0;
    if (a < b) { r = 1; } else { r = 0; }
    printf("%s = %f\n", "a", a);
    printf("%s = %f\n", "b", b);
    printf("%s = %ld\n", "r", r);
    return 0;
}
