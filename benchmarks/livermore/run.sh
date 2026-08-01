#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Livermore Loops benchmark: WhileLang compiler vs C (clang)
#
# Usage:  ./run.sh            — build and run all benchmarks
#         ./run.sh k03_dot    — run only one kernel
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
BUILD_DIR="$SCRIPT_DIR/build"

mkdir -p "$BUILD_DIR"

# ── helpers ────────────────────────────────────────────────────

time_cmd() {
  # Returns wall-clock seconds (requires Python 3)
  python3 -c "
import subprocess, sys, time
start = time.monotonic()
subprocess.run(sys.argv[1:], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
end = time.monotonic()
print(f'{end - start:.6f}')
" "$@"
}

# ── build compiler ─────────────────────────────────────────────

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building WhileLang compiler …"
  (cd "$PROJ_DIR" && lake build compiler 2>&1 | tail -1)
fi

# ── determine which kernels to run ─────────────────────────────

if [ $# -gt 0 ]; then
  KERNELS=("$@")
else
  KERNELS=()
  for f in "$SCRIPT_DIR"/k*.w; do
    KERNELS+=("$(basename "$f" .w)")
  done
fi

# ── compile ────────────────────────────────────────────────────

echo "Compiling …"
for name in "${KERNELS[@]}"; do
  wfile="$SCRIPT_DIR/${name}.w"
  cfile="$SCRIPT_DIR/${name}.c"

  if [ -f "$cfile" ]; then
    cc -O0 -o "$BUILD_DIR/${name}_c_O0" "$cfile" 2>/dev/null
    cc -O2 -o "$BUILD_DIR/${name}_c_O2" "$cfile" 2>/dev/null
  fi

  if [ -f "$wfile" ]; then
    "$COMPILER" "$wfile" -o "$BUILD_DIR/${name}_wl" 2>/dev/null || \
      echo "  !! WhileLang compile failed: $name"
  fi
done

# ── run benchmarks ─────────────────────────────────────────────

echo ""
printf "%-18s  %10s  %10s  %10s  %8s\n" \
       "Kernel" "C -O0 (s)" "C -O2 (s)" "WL (s)" "WL/C-O2"
printf "%-18s  %10s  %10s  %10s  %8s\n" \
       "──────────────" "─────────" "─────────" "─────────" "───────"

for name in "${KERNELS[@]}"; do
  t_o0="—"
  t_o2="—"
  t_wl="—"
  ratio="—"

  if [ -x "$BUILD_DIR/${name}_c_O0" ]; then
    t_o0=$(time_cmd "$BUILD_DIR/${name}_c_O0")
  fi
  if [ -x "$BUILD_DIR/${name}_c_O2" ]; then
    t_o2=$(time_cmd "$BUILD_DIR/${name}_c_O2")
  fi
  if [ -x "$BUILD_DIR/${name}_wl" ]; then
    t_wl=$(time_cmd "$BUILD_DIR/${name}_wl")
  fi

  # compute ratio WL / C-O2
  if [ "$t_o2" != "—" ] && [ "$t_wl" != "—" ]; then
    ratio=$(python3 -c "print(f'{float(\"$t_wl\")/float(\"$t_o2\"):.1f}x')")
  fi

  printf "%-18s  %10s  %10s  %10s  %8s\n" "$name" "$t_o0" "$t_o2" "$t_wl" "$ratio"
done

echo ""
echo "C timing is external (includes init); C programs also print internal kernel-only time."
echo "WL timing is external (includes init + observable printing)."
echo "Init is ≤0.01% of kernel time at these rep counts."
