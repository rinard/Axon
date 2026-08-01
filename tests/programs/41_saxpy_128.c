#include <stdio.h>
#include <stdint.h>
int64_t X[1024], Y[1024];
int main() {
    int64_t n = 0, a = 0, i = 0, checksum = 0;
    n = 128;
    a = 7;
    i = 0;
    while (i < n) {
        X[i] = i * 3 + 1;
        Y[i] = i * 2 + 5;
        i = i + 1;
    }
    i = 0;
    while (i < n) {
        Y[i] = a * X[i] + Y[i];
        i = i + 1;
    }
    checksum = 0;
    i = 0;
    while (i < n) {
        checksum = checksum + Y[i];
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "checksum", checksum);
    return 0;
}
