#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Sweep a 'kind' over increasing sizes; report compile time, instr count, and
# whether While output matches C. Stops after first failure (plus a couple beyond).
# Usage: scale_sweep.sh <kind> <sizes...>
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COMPILER="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/compiler"
RT="$ROOT/Compiler/runtime.c"
TMP=$(mktemp -d); trap "rm -rf $TMP" EXIT
kind="$1"; shift
printf "%-6s %-7s %-10s %-9s %-8s %-10s %s\n" KIND SIZE COMPILE_s ARM_INSTR WHILE_rc MATCH NOTE
for n in "$@"; do
  stem="$TMP/s_${kind}_${n}"
  python3 "$ROOT/stress/gen_scale.py" "$kind" "$n" "$stem"
  # compile while -> asm (capture stage markers for arm instr count + total time)
  t0=$(python3 -c 'import time;print(time.time())')
  if ! $COMPILER "$stem.w" -S "$stem.s" >"$stem.log" 2>&1; then
    comp_s=$(python3 -c "import time;print(f'{time.time()-$t0:.2f}')")
    note=$(grep -iE "error|fail|exceed|not well" "$stem.log" | head -1 | cut -c1-50)
    printf "%-6s %-7s %-10s %-9s %-8s %-10s %s\n" "$kind" "$n" "$comp_s" "-" "-" "COMPILE-FAIL" "$note"
    continue
  fi
  comp_s=$(python3 -c "import time;print(f'{time.time()-$t0:.2f}')")
  arm=$(grep -oE "arm_instrs=[0-9]+" "$stem.log" | head -1 | cut -d= -f2)
  # assemble+link
  if ! cc -o "$stem.bin" "$stem.s" "$RT" 2>"$stem.asmerr"; then
    note=$(head -1 "$stem.asmerr" | cut -c1-50)
    printf "%-6s %-7s %-10s %-9s %-8s %-10s %s\n" "$kind" "$n" "$comp_s" "${arm:--}" "-" "ASM-FAIL" "$note"
    continue
  fi
  # run while
  "$stem.bin" > "$stem.wout" 2>&1 &
  wp=$!; ( sleep 40; kill $wp 2>/dev/null ) & tp=$!
  wait $wp 2>/dev/null; wrc=$?; kill $tp 2>/dev/null; wait $tp 2>/dev/null
  # compile+run C oracle
  cc -O2 -w -o "$stem.cbin" "$stem.c" 2>/dev/null
  "$stem.cbin" > "$stem.cout" 2>&1
  match="MATCH"
  if [ "$wrc" -ne 0 ]; then match="WHILE-RC=$wrc"; fi
  if ! diff -q "$stem.wout" "$stem.cout" >/dev/null 2>&1; then
    match="MISMATCH"
  fi
  printf "%-6s %-7s %-10s %-9s %-8s %-10s\n" "$kind" "$n" "$comp_s" "${arm:--}" "$wrc" "$match"
done
