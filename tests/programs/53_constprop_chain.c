#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, c = 0, d = 0, e = 0;
    a = 2;
    b = (int64_t)((uint64_t)a + (uint64_t)3);
    c = (int64_t)((uint64_t)b * (uint64_t)4);
    d = (int64_t)((uint64_t)c - (uint64_t)1);
    e = d / 3;
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "d", d);
    printf("%s = %ld\n", "e", e);
    return 0;
}
