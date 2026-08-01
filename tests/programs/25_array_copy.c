#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int64_t B[1024];
int main() {
    int64_t n = 0, i = 0, s = 0;
    n = 4;
    A[0] = 11;
    A[1] = 22;
    A[2] = 33;
    A[3] = 44;
    i = 0;
    while (i < n) {
        B[i] = A[i];
        i = i + 1;
    }
    s = B[0] + B[1] + B[2] + B[3];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "s", s);
    return 0;
}
