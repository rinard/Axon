#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, c = 0, i = 0, s = 0;
    a = 3;
    b = 7;
    c = (int64_t)((uint64_t)a + (uint64_t)b);
    i = 0;
    s = 0;
    while (i < 5) {
        s = (int64_t)((uint64_t)s + (uint64_t)((int64_t)((uint64_t)a + (uint64_t)b)));
        i = (int64_t)((uint64_t)i + (uint64_t)1);
    }
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "s", s);
    return 0;
}
