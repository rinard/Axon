#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, q = 0, r = 0;
    a = 17;
    b = 5;
    q = a / b;
    r = a % b;
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "q", q);
    printf("%s = %ld\n", "r", r);
    return 0;
}
