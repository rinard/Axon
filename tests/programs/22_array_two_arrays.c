#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int64_t B[1024];
int main() {
    int64_t i = 0, s = 0;
    A[0] = 1;
    A[1] = 2;
    A[2] = 3;
    B[0] = 10;
    B[1] = 20;
    B[2] = 30;
    s = 0;
    i = 0;
    while (i < 3) {
        s = s + A[i] * B[i];
        i = i + 1;
    }
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "s", s);
    return 0;
}
