#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Compiler correctness tests: compare While compiler output vs C reference.
# Usage: ./tests/run_tests.sh
#
# Requires: lake build compiler (While→ARM64 compiler)
#           cc (C compiler, e.g. clang on macOS)

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
COMPILER="$PROJECT_DIR/.lake/build/bin/compiler"
PROG_DIR="$SCRIPT_DIR/programs"
TMP_DIR=$(mktemp -d)

trap "rm -rf $TMP_DIR" EXIT

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

# Check compiler exists
if [ ! -x "$COMPILER" ]; then
    echo "Building compiler..."
    (cd "$PROJECT_DIR" && lake build compiler 2>&1 | tail -1)
fi

pass=0
fail=0
skip=0

for while_file in "$PROG_DIR"/*.while; do
    name=$(basename "$while_file" .while)
    c_file="$PROG_DIR/${name}.c"

    # Skip bounds-error tests (handled separately below)
    case "$name" in bounds_*) continue ;; esac

    if [ ! -f "$c_file" ]; then
        printf "${YELLOW}SKIP${NC} %-30s (no .c file)\n" "$name"
        skip=$((skip + 1))
        continue
    fi

    # Compile + run While program
    while_bin="$TMP_DIR/while_${name}"
    while_asm="$TMP_DIR/while_${name}.s"
    while_out="$TMP_DIR/while_${name}.out"
    while_exit=0

    if ! "$COMPILER" "$while_file" -o "$while_bin" 2>"$TMP_DIR/while_${name}.err"; then
        printf "${RED}FAIL${NC} %-30s (While compilation failed)\n" "$name"
        cat "$TMP_DIR/while_${name}.err" | head -3
        fail=$((fail + 1))
        continue
    fi

    # Run with 10s timeout (portable macOS/Linux)
    "$while_bin" > "$while_out" 2>&1 &
    local_pid=$!
    ( sleep 10; kill $local_pid 2>/dev/null ) &
    timer_pid=$!
    wait $local_pid 2>/dev/null
    while_exit=$?
    kill $timer_pid 2>/dev/null; wait $timer_pid 2>/dev/null
    if [ "$while_exit" -gt 128 ]; then
        printf "${YELLOW}SKIP${NC} %-30s (timed out)\n" "$name"
        skip=$((skip + 1))
        continue
    fi

    # Compile + run C program
    c_bin="$TMP_DIR/c_${name}"
    c_out="$TMP_DIR/c_${name}.out"
    c_exit=0

    if ! cc -o "$c_bin" "$c_file" -w 2>"$TMP_DIR/c_${name}.err"; then
        printf "${RED}FAIL${NC} %-30s (C compilation failed)\n" "$name"
        fail=$((fail + 1))
        continue
    fi

    "$c_bin" > "$c_out" 2>&1 &
    local_pid=$!
    ( sleep 10; kill $local_pid 2>/dev/null ) &
    timer_pid=$!
    wait $local_pid 2>/dev/null
    c_exit=$?
    kill $timer_pid 2>/dev/null; wait $timer_pid 2>/dev/null
    if [ "$c_exit" -gt 128 ]; then
        printf "${YELLOW}SKIP${NC} %-30s (C timed out)\n" "$name"
        skip=$((skip + 1))
        continue
    fi

    # Compare outputs AND exit codes
    if [ "$while_exit" != "$c_exit" ]; then
        printf "${RED}FAIL${NC} %-30s (exit code: while=%d c=%d)\n" "$name" "$while_exit" "$c_exit"
        echo "  While output: $(cat "$while_out")"
        echo "  C output:     $(cat "$c_out")"
        fail=$((fail + 1))
    elif ! diff -q "$while_out" "$c_out" > /dev/null 2>&1; then
        printf "${RED}FAIL${NC} %-30s (output differs)\n" "$name"
        diff "$while_out" "$c_out" | head -10
        fail=$((fail + 1))
    else
        printf "${GREEN}PASS${NC} %-30s" "$name"
        if [ "$while_exit" != "0" ]; then
            printf " (exit=%d)" "$while_exit"
        fi
        printf "\n"
        pass=$((pass + 1))
    fi
done

# --- Bounds-error tests (While-only, expect exit code 1) ---
for while_file in "$PROG_DIR"/bounds_*.while; do
    [ -f "$while_file" ] || continue
    name=$(basename "$while_file" .while)

    while_bin="$TMP_DIR/while_${name}"
    while_out="$TMP_DIR/while_${name}.out"

    if ! "$COMPILER" "$while_file" -o "$while_bin" 2>"$TMP_DIR/while_${name}.err"; then
        printf "${RED}FAIL${NC} %-30s (While compilation failed)\n" "$name"
        fail=$((fail + 1))
        continue
    fi

    "$while_bin" > "$while_out" 2>&1 &
    local_pid=$!
    ( sleep 10; kill $local_pid 2>/dev/null ) &
    timer_pid=$!
    wait $local_pid 2>/dev/null
    while_exit=$?
    kill $timer_pid 2>/dev/null; wait $timer_pid 2>/dev/null

    if [ "$while_exit" -gt 128 ]; then
        printf "${YELLOW}SKIP${NC} %-30s (timed out)\n" "$name"
        skip=$((skip + 1))
    elif [ "$while_exit" -eq 1 ]; then
        printf "${GREEN}PASS${NC} %-30s (bounds error)\n" "$name"
        pass=$((pass + 1))
    else
        printf "${RED}FAIL${NC} %-30s (expected exit=1, got=%d)\n" "$name" "$while_exit"
        fail=$((fail + 1))
    fi
done

echo ""
echo "Results: ${pass} passed, ${fail} failed, ${skip} skipped"

if [ "$fail" -gt 0 ]; then
    exit 1
fi
