/* Copyright (c) 2026 Martin Rinard */
/* Runtime stubs for typed-print library calls.
 *
 * The compiler emits `bl _printInt` / `_printBool` / `_printFloat` /
 * `_printString` instructions; this file provides the underlying C
 * implementations. The leading underscore is added by the macOS/ARM64
 * linker convention (Mach-O) — define them without the underscore in C.
 *
 * Print* functions print *only the value* — no automatic newline. Source
 * programs emit newlines explicitly via `printString("\n")`.
 */

#include <stdio.h>
#include <stdint.h>

void printInt(int64_t v)        { printf("%ld", (long)v); }
void printBool(int64_t v)       { printf("%s", v ? "true" : "false"); }
void printFloat(double f)       { printf("%f", f); }
void printString(const char *s) { fputs(s, stdout); }
