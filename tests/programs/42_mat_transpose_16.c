#include <stdio.h>
#include <stdint.h>
int64_t A[1024], B[1024];
int main() {
    int64_t n = 0, i = 0, j = 0, checksum = 0;
    n = 16;
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            A[i * n + j] = i * 100 + j;
            j = j + 1;
        }
        i = i + 1;
    }
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            B[j * n + i] = A[i * n + j];
            j = j + 1;
        }
        i = i + 1;
    }
    checksum = 0;
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            checksum = checksum + B[i * n + j];
            j = j + 1;
        }
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "checksum", checksum);
    return 0;
}
