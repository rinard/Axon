#include <stdio.h>
#include <stdint.h>
int64_t A[16];
int main() {
    int64_t a = 0, b = 0, c = 0, d = 0, i = 0;
    a = 3;
    b = 5;
    i = 0;
    while (i < 8) {
        c = (int64_t)((uint64_t)a * (uint64_t)b);
        A[i] = c;
        d = (int64_t)((uint64_t)a * (uint64_t)b);
        i = (int64_t)((uint64_t)i + (uint64_t)1);
    }
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "d", d);
    printf("%s = %ld\n", "i", i);
    return 0;
}
