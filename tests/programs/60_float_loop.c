#include <stdio.h>
#include <stdint.h>
int main() {
    double x = 0;
    int64_t i = 0;
    x = 0.0;
    i = 0;
    while (i < 5) {
        x = x + 1.5;
        i = i + 1;
    }
    printf("%s = %f\n", "x", x);
    printf("%s = %ld\n", "i", i);
    return 0;
}
