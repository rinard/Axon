#include <stdio.h>
#include <stdint.h>
int64_t grid[16];
int main() {
    int64_t r = 0, c = 0, idx = 0, ondiag = 0;
    r = 0;
    while (r < 4) {
        c = 0;
        while (c < 4) {
            idx = r * 4 + c;
            if (r == c) { grid[idx] = 1; } else { grid[idx] = 0; }
            c = c + 1;
        }
        r = r + 1;
    }
    r = 0;
    ondiag = 0;
    while (r < 4) {
        c = 0;
        while (c < 4) {
            idx = r * 4 + c;
            if (grid[idx]) { ondiag = ondiag + 1; } else { ondiag = ondiag + 0; }
            c = c + 1;
        }
        r = r + 1;
    }
    printf("diag=%ld\n", (long)ondiag);
    return 0;
}
