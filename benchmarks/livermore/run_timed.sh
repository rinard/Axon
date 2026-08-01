#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Run Livermore Loops with kernel-only timing for WL (instrumented .s files)
# and compare against Fortran ref, C -O0, C -O2 (internal timing)
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUILD_DIR="$SCRIPT_DIR/build"
TIMED_DIR="$BUILD_DIR/timed"

# ── helpers ────────────────────────────────────────────────────
TIMEOUT=60  # seconds per benchmark run

run_with_timeout() {
  local pid
  "$@" &
  pid=$!
  ( sleep $TIMEOUT && kill $pid 2>/dev/null ) &
  local watchdog=$!
  wait $pid 2>/dev/null
  local ret=$?
  kill $watchdog 2>/dev/null
  wait $watchdog 2>/dev/null
  return $ret
}

extract_kernel_ticks() {
  local output
  output=$(run_with_timeout "$1" 2>&1) || true
  local ticks
  ticks=$(echo "$output" | grep -o 'kernel_ticks: [0-9]*' | grep -o '[0-9]*')
  if [ -n "$ticks" ]; then
    python3 -c "print(f'{int(\"$ticks\") * 125 / 3 / 1e9:.6f}')"
  else
    echo "—"
  fi
}

extract_c_internal() {
  local output
  output=$(run_with_timeout "$1" 2>&1) || true
  local elapsed
  elapsed=$(echo "$output" | grep -oE '(elapsed|Time): [0-9.]+' | grep -oE '[0-9.]+')
  if [ -n "$elapsed" ]; then
    echo "$elapsed"
  else
    echo "—"
  fi
}

# ── compile if needed ─────────────────────────────────────────
echo "Compiling..."
for cfile in "$SCRIPT_DIR"/k[0-9]*.c; do
  [ -f "$cfile" ] || continue
  name=$(basename "$cfile" .c)
  [[ "$name" == *_ref ]] && continue
  [ -x "$BUILD_DIR/${name}_c_O0" ] || cc -O0 -lm -o "$BUILD_DIR/${name}_c_O0" "$cfile" 2>/dev/null || true
  [ -x "$BUILD_DIR/${name}_c_O2" ] || cc -O2 -lm -o "$BUILD_DIR/${name}_c_O2" "$cfile" 2>/dev/null || true
done
for cfile in "$SCRIPT_DIR"/k*_ref.c; do
  [ -f "$cfile" ] || continue
  name=$(basename "$cfile" .c)
  [ -x "$BUILD_DIR/${name}" ] || cc -O2 -lm -o "$BUILD_DIR/${name}" "$cfile" 2>/dev/null || true
done

# ── determine kernels ────────────────────────────────────────
KERNELS=()
for f in "$SCRIPT_DIR"/k*.w; do
  KERNELS+=("$(basename "$f" .w)")
done

# ── run benchmarks ────────────────────────────────────────────
echo ""
printf "%-22s  %10s  %10s  %10s  %10s  %10s  %10s\n" \
       "Kernel" "Ref (s)" "C -O0 (s)" "C -O2 (s)" "WL (s)" "WL/C-O0" "WL/C-O2"
printf "%-22s  %10s  %10s  %10s  %10s  %10s  %10s\n" \
       "──────────────────" "─────────" "─────────" "─────────" "─────────" "───────" "───────"

for name in "${KERNELS[@]}"; do
  t_ref="—"
  t_o0="—"
  t_o2="—"
  t_wl="—"
  ratio_o0="—"
  ratio_o2="—"

  # Extract kernel number for ref file (e.g., k01_hydro -> k01)
  knum=$(echo "$name" | grep -oE '^k[0-9]+')
  if [ -x "$BUILD_DIR/${knum}_ref" ]; then
    t_ref=$(extract_c_internal "$BUILD_DIR/${knum}_ref")
  fi
  if [ -x "$BUILD_DIR/${name}_c_O0" ]; then
    t_o0=$(extract_c_internal "$BUILD_DIR/${name}_c_O0")
  fi
  if [ -x "$BUILD_DIR/${name}_c_O2" ]; then
    t_o2=$(extract_c_internal "$BUILD_DIR/${name}_c_O2")
  fi
  if [ -x "$TIMED_DIR/${name}_wl" ]; then
    t_wl=$(extract_kernel_ticks "$TIMED_DIR/${name}_wl")
  fi

  if [ "$t_o0" != "—" ] && [ "$t_wl" != "—" ]; then
    ratio_o0=$(python3 -c "print(f'{float(\"$t_wl\")/float(\"$t_o0\"):.1f}x')")
  fi
  if [ "$t_o2" != "—" ] && [ "$t_wl" != "—" ]; then
    ratio_o2=$(python3 -c "print(f'{float(\"$t_wl\")/float(\"$t_o2\"):.1f}x')")
  fi

  printf "%-22s  %10s  %10s  %10s  %10s  %10s  %10s\n" \
         "$name" "$t_ref" "$t_o0" "$t_o2" "$t_wl" "$ratio_o0" "$ratio_o2"
done

echo ""
echo "Ref:  Fortran-faithful C reference, compiled with -O2 (kernel-only timing)"
echo "C:    Our C translation, compiled with clang -O0 / -O2 (kernel-only timing)"
echo "WL:   WhileLang compiler output, kernel-only timing via CNTVCT_EL0"
echo "All times exclude initialization."
