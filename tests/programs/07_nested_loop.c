#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t i = 0, j = 0, s = 0;
    s = 0;
    i = 0;
    while (i < 10) {
        j = 0;
        while (j < 10) {
            s = s + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "s", s);
    return 0;
}
