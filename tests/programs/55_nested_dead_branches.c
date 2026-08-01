#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, c = 0, r = 0;
    a = 1;
    b = 2;
    c = 3;
    if (a == 1) {
        if (b == 2) {
            if (c == 3) {
                r = 111;
            } else {
                r = 222;
            }
        } else {
            r = 333;
        }
    } else {
        r = 444;
    }
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "r", r);
    return 0;
}
