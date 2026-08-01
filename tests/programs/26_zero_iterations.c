#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, i = 0;
    x = 0;
    i = 10;
    while (i < 5) {
        x = x + 1;
        i = i + 1;
    }
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "i", i);
    return 0;
}
