#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t n = 0, i = 0, s = 0;
    n = 5;
    A[0] = 10;
    A[1] = 20;
    A[2] = 30;
    A[3] = 40;
    A[4] = 50;
    s = 0;
    i = 0;
    while (i < n) {
        s = s + A[i];
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "s", s);
    return 0;
}
