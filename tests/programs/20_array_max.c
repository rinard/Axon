#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t n = 0, i = 0, m = 0;
    n = 6;
    A[0] = 3;
    A[1] = 7;
    A[2] = 1;
    A[3] = 9;
    A[4] = 2;
    A[5] = 5;
    m = A[0];
    i = 1;
    while (i < n) {
        if (A[i] > m) { m = A[i]; }
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "m", m);
    return 0;
}
