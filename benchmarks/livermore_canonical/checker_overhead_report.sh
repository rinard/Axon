#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Re-runs the canonical Livermore Loops with the instrumented compiler,
# parses per-pass [PASS] lines (which now carry analyze_us / check_us /
# total us=), and prints checker overhead as a percentage of optimisation
# time, broken out per pass.
#
# Usage:  ./checker_overhead_report.sh                — all kernels
#         ./checker_overhead_report.sh k03_dot k15_casual
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$SCRIPT_DIR/build_checker_overhead"

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "compiler binary missing — run lake build compiler first" >&2
  exit 1
fi

if [ $# -gt 0 ]; then
  KERNELS=("$@")
else
  KERNELS=()
  for f in "$SCRIPT_DIR"/k*.w; do
    KERNELS+=("$(basename "$f" .w)")
  done
fi

echo "Compiling ${#KERNELS[@]} kernel(s) ..."
for name in "${KERNELS[@]}"; do
  wfile="$SCRIPT_DIR/${name}.w"
  asm="$OUT_DIR/${name}.s"
  log="$OUT_DIR/${name}.log"
  [ -f "$wfile" ] || { echo "  skip $name (no .w)"; continue; }
  if ! "$COMPILER" "$wfile" -S "$asm" 2> "$log" >/dev/null; then
    echo "  fail $name"
  fi
done

echo ""
echo "================================================================================"
echo "Per-pass aggregate across all kernels — analyze vs check"
echo "================================================================================"
echo ""

awk '
  function field(line, key,   i, n, parts, k) {
    n = split(line, parts, " ")
    k = key "="
    for (i = 1; i <= n; i++) if (substr(parts[i], 1, length(k)) == k) {
      return substr(parts[i], length(k) + 1)
    }
    return ""
  }
  /\[PASS\]/ {
    phase = field($0, "phase")
    name  = field($0, "name")
    a = field($0, "analyze_us") + 0
    c = field($0, "check_us") + 0
    u = field($0, "us") + 0
    key = phase ":" name
    a_total[key] += a
    c_total[key] += c
    u_total[key] += u
    count[key]   += 1
    g_a += a; g_c += c; g_u += u
  }
  END {
    n = 0
    for (k in u_total) keys[++n] = k
    # Sort by total time descending
    for (i = 1; i <= n; i++)
      for (j = i + 1; j <= n; j++)
        if (u_total[keys[i]] < u_total[keys[j]]) {
          t = keys[i]; keys[i] = keys[j]; keys[j] = t
        }
    printf "%-26s %5s %12s %12s %12s %8s\n", \
      "phase:name", "calls", "total ms", "analyze ms", "check ms", "% check"
    printf "%-26s %5s %12s %12s %12s %8s\n", \
      "──────────", "─────", "────────", "──────────", "────────", "───────"
    for (i = 1; i <= n; i++) {
      k = keys[i]
      pct = (u_total[k] > 0) ? (100.0 * c_total[k] / u_total[k]) : 0
      printf "%-26s %5d %12.1f %12.1f %12.1f %7.1f%%\n", \
        k, count[k], u_total[k]/1000.0, a_total[k]/1000.0, \
        c_total[k]/1000.0, pct
    }
    printf "%-26s %5s %12s %12s %12s %8s\n", \
      "──────────", "─────", "────────", "──────────", "────────", "───────"
    pct = (g_u > 0) ? (100.0 * g_c / g_u) : 0
    printf "%-26s %5s %12.1f %12.1f %12.1f %7.1f%%\n", \
      "TOTAL (sum of passes)", "", g_u/1000.0, g_a/1000.0, g_c/1000.0, pct
  }
' "$OUT_DIR"/*.log

echo ""
echo "Logs: $OUT_DIR"
