#include <stdio.h>
#include <stdint.h>
int64_t A[8];
int main() {
    int64_t a = 0, b = 0, c = 0, d = 0;
    a = 3;
    b = 7;
    c = (int64_t)((uint64_t)a + (uint64_t)b);
    A[0] = 99;
    a = A[0];
    d = (int64_t)((uint64_t)a + (uint64_t)b);
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "d", d);
    return 0;
}
