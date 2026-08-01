#include <stdio.h>
#include <stdint.h>
int64_t flags[4];
int main() {
    int64_t i = 0;
    flags[0] = 1;
    flags[1] = 0;
    flags[2] = 1;
    flags[3] = 0;
    i = 0;
    while (i < 4) {
        printf("%s\n", flags[i] ? "true" : "false");
        i = i + 1;
    }
    return 0;
}
