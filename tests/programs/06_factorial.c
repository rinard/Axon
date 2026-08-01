#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t n = 0, r = 0;
    n = 12;
    r = 1;
    while (n != 0) {
        r = r * n;
        n = n - 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "r", r);
    return 0;
}
