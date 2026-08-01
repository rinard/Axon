#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Pipeline instrumentation report for canonical Livermore Loops.
# Compiles each kernel with -S, captures the [PASS]/[CLUSTER]/[STAGE]/[TOTAL]
# marker lines emitted by the instrumented driver, and prints:
#   1. Per-kernel summary (total compile time, per-stage time, cluster iters)
#   2. Per-pass aggregate (count + total + avg microseconds across all kernels)
#
# Usage:  ./run_pipeline_report.sh                 — all kernels
#         ./run_pipeline_report.sh k03_dot k21_matmul
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$SCRIPT_DIR/build_pipeline_report"

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building compiler …"
  (cd "$PROJ_DIR" && lake build compiler 2>&1 | tail -1)
fi

if [ $# -gt 0 ]; then
  KERNELS=("$@")
else
  KERNELS=()
  for f in "$SCRIPT_DIR"/k*.w; do
    KERNELS+=("$(basename "$f" .w)")
  done
fi

echo "Compiling ${#KERNELS[@]} kernel(s) and collecting instrumentation logs ..."
fail=()
for name in "${KERNELS[@]}"; do
  wfile="$SCRIPT_DIR/${name}.w"
  asm="$OUT_DIR/${name}.s"
  log="$OUT_DIR/${name}.log"
  if [ ! -f "$wfile" ]; then
    fail+=("$name (no .w file)")
    continue
  fi
  if ! "$COMPILER" "$wfile" -S "$asm" 2> "$log" >/dev/null; then
    fail+=("$name (compile failed)")
  fi
done

if [ ${#fail[@]} -gt 0 ]; then
  echo "  !! Failures:"
  printf "       %s\n" "${fail[@]}"
fi

echo ""
echo "================================================================================"
echo "Per-kernel pipeline summary (times in milliseconds, sizes in instructions)"
echo "================================================================================"
echo ""
printf "%-22s %8s %8s %8s %8s %8s %4s %3s %5s %5s %5s\n" \
  "Kernel" "Total" "Parse" "TAC" "Opt" "Codegen" "Iter" "FP" "TAC0" "TAC1" "ARM"
printf "%-22s %8s %8s %8s %8s %8s %4s %3s %5s %5s %5s\n" \
  "──────" "─────" "─────" "─────" "─────" "───────" "────" "───" "────" "────" "───"

for name in "${KERNELS[@]}"; do
  log="$OUT_DIR/${name}.log"
  if [ ! -f "$log" ]; then
    printf "%-22s %s\n" "$name" "(missing log)"
    continue
  fi
  awk -v name="$name" '
    function us_field(line,    i, n, parts) {
      n = split(line, parts, " ")
      for (i = 1; i <= n; i++) if (parts[i] ~ /^us=/) { sub(/^us=/, "", parts[i]); return parts[i] + 0 }
      return 0
    }
    function field(line, key,    i, n, parts, k) {
      n = split(line, parts, " ")
      k = key "="
      for (i = 1; i <= n; i++) if (substr(parts[i], 1, length(k)) == k) {
        return substr(parts[i], length(k) + 1)
      }
      return ""
    }
    /\[STAGE\] name=parse / { parse = us_field($0) }
    /\[STAGE\] name=compileToTAC / { tac_us = us_field($0); tac0 = field($0, "tac_size") }
    /\[STAGE\] name=optimize / { opt = us_field($0); tac1 = field($0, "opt_size") }
    /\[STAGE\] name=verifiedCodegen / { cg = us_field($0); arm = field($0, "arm_instrs") }
    /\[CLUSTER\]/ { iter = field($0, "iters"); fp = field($0, "fixedPoint") }
    /\[TOTAL\]/ { total = field($0, "compile_us") + 0 }
    END {
      if (total == "") { printf "%-22s %s\n", name, "(no [TOTAL])"; exit }
      fp_short = (fp == "true") ? "yes" : "no"
      printf "%-22s %8.2f %8.2f %8.2f %8.2f %8.2f %4s %3s %5s %5s %5s\n",
        name, total/1000, parse/1000, tac_us/1000, opt/1000, cg/1000,
        iter, fp_short, tac0, tac1, arm
    }
  ' "$log"
done

echo ""
echo "================================================================================"
echo "Per-pass aggregate (sum across all listed kernels)"
echo "================================================================================"
echo ""

awk '
  function field(line, key,    i, n, parts, k) {
    n = split(line, parts, " ")
    k = key "="
    for (i = 1; i <= n; i++) if (substr(parts[i], 1, length(k)) == k) {
      return substr(parts[i], length(k) + 1)
    }
    return ""
  }
  /\[PASS\]/ {
    phase = field($0, "phase")
    name = field($0, "name")
    us = field($0, "us") + 0
    siz_in = field($0, "size_in") + 0
    siz_out = field($0, "size_out") + 0
    key = phase ":" name
    total[key] += us
    count[key] += 1
    delta[key] += (siz_out - siz_in)
    if (!(key in order_seen)) {
      order_seen[key] = ++ord
    }
  }
  END {
    printf "%-26s %6s %12s %10s %10s\n", "phase:name", "calls", "us total", "us avg", "Δsize"
    printf "%-26s %6s %12s %10s %10s\n", "──────────", "─────", "────────", "──────", "─────"
    # Print in ascending us-total order
    n = 0
    for (k in total) { keys[++n] = k }
    # bubble sort
    for (i = 1; i <= n; i++)
      for (j = i + 1; j <= n; j++)
        if (total[keys[i]] > total[keys[j]]) {
          tmp = keys[i]; keys[i] = keys[j]; keys[j] = tmp
        }
    grand = 0
    for (i = 1; i <= n; i++) {
      k = keys[i]
      printf "%-26s %6d %12d %10d %+10d\n", k, count[k], total[k], total[k]/count[k], delta[k]
      grand += total[k]
    }
    printf "%-26s %6s %12d\n", "TOTAL pass time", "", grand
  }
' "$OUT_DIR"/*.log

echo ""
echo "Logs and assembly per kernel: $OUT_DIR"
