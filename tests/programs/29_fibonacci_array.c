#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t n = 0, i = 0, r = 0;
    n = 20;
    A[0] = 0;
    A[1] = 1;
    i = 2;
    while (i <= n) {
        A[i] = A[i - 1] + A[i - 2];
        i = i + 1;
    }
    r = A[n];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "r", r);
    return 0;
}
