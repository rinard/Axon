#include <stdio.h>
#include <stdint.h>
int64_t A[1024], B[1024], C[1024];
int main() {
    int64_t n = 0, i = 0, j = 0, k = 0, s = 0, trace = 0;
    n = 8;
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            A[i * n + j] = i * n + j + 1;
            B[i * n + j] = (i + j) % 7 + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            s = 0;
            k = 0;
            while (k < n) {
                s = s + A[i * n + k] * B[k * n + j];
                k = k + 1;
            }
            C[i * n + j] = s;
            j = j + 1;
        }
        i = i + 1;
    }
    trace = 0;
    i = 0;
    while (i < n) {
        trace = trace + C[i * n + i];
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "k", k);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "trace", trace);
    return 0;
}
