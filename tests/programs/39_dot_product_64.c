#include <stdio.h>
#include <stdint.h>
int64_t A[1024], B[1024];
int main() {
    int64_t n = 0, i = 0, dot = 0;
    n = 64;
    i = 0;
    while (i < n) {
        A[i] = i + 1;
        B[i] = n - i;
        i = i + 1;
    }
    dot = 0;
    i = 0;
    while (i < n) {
        dot = dot + A[i] * B[i];
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "dot", dot);
    return 0;
}
