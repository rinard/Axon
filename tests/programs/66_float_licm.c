#include <stdio.h>
#include <stdint.h>
int main() {
    double a = 0, b = 0, c = 0, s = 0;
    int64_t i = 0;
    a = 2.0;
    b = 3.0;
    c = a * b;
    i = 0;
    s = 0.0;
    while (i < 4) {
        s = s + (a * b);
        i = (int64_t)((uint64_t)i + (uint64_t)1);
    }
    printf("%s = %f\n", "a", a);
    printf("%s = %f\n", "b", b);
    printf("%s = %f\n", "c", c);
    printf("%s = %ld\n", "i", i);
    printf("%s = %f\n", "s", s);
    return 0;
}
