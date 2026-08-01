#include <stdio.h>
#include <stdint.h>
int64_t X[1024], Y[1024];
int main() {
    int64_t n = 0, a = 0, i = 0, r = 0;
    n = 6;
    a = 3;
    X[0] = 1; X[1] = 2; X[2] = 3; X[3] = 4; X[4] = 5; X[5] = 6;
    Y[0] = 10; Y[1] = 20; Y[2] = 30; Y[3] = 40; Y[4] = 50; Y[5] = 60;
    i = 0;
    while (i < n) {
        Y[i] = a * X[i] + Y[i];
        i = i + 1;
    }
    r = Y[0] * 100000 + Y[1] * 10000 + Y[2] * 1000 + Y[3] * 100 + Y[4] * 10 + Y[5];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "r", r);
    return 0;
}
