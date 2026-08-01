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
        if (!flags[i]) { printf("not-true\n"); } else { printf("yes\n"); }
        i = i + 1;
    }
    return 0;
}
