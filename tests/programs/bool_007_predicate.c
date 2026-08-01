#include <stdio.h>
#include <stdint.h>
int64_t isEven[10];
int main() {
    int64_t i = 0, sum = 0;
    i = 0;
    while (i < 10) {
        if (i / 2 * 2 == i) { isEven[i] = 1; } else { isEven[i] = 0; }
        i = i + 1;
    }
    i = 0;
    sum = 0;
    while (i < 10) {
        if (isEven[i]) { sum = sum + i; } else { sum = sum + 0; }
        i = i + 1;
    }
    printf("sum_evens=%ld\n", (long)sum);
    return 0;
}
