#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t i = 0, s = 0;
    i = 0;
    while (i < 10) {
        A[i] = i * i;
        i = i + 1;
    }
    s = A[3] + A[7];
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "s", s);
    return 0;
}
