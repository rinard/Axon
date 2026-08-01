#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t n = 0, s = 0, i = 0;
    n = 100;
    s = 0;
    i = 1;
    while (i <= n) {
        s = s + i;
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "i", i);
    return 0;
}
