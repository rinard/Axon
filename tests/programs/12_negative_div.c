#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, q = 0, r = 0, q2 = 0, r2 = 0;
    a = -17;
    b = 5;
    q = a / b;
    r = a % b;
    q2 = 17 / (-5);
    r2 = 17 % (-5);
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "q", q);
    printf("%s = %ld\n", "r", r);
    printf("%s = %ld\n", "q2", q2);
    printf("%s = %ld\n", "r2", r2);
    return 0;
}
