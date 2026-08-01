#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Csmith-style random differential campaign: generate N random While programs +
# matching C, compile/run both, compare. Divergence (with C as the by-construction
# oracle) = miscompile. Also flags While compile/run failures and cert rejections.
# Usage: csmith_campaign.sh <count> [start_seed]
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
C="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/compiler"
CA="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/certaudit"
GEN="$ROOT/stress/csmith_gen.py"
N="${1:-100}"; START="${2:-1}"
D=$(mktemp -d); trap "rm -rf $D" EXIT
pass=0; diff=0; wfail=0; cfail=0; rej=0
for s in $(seq "$START" $((START+N-1))); do
  python3 "$GEN" "$s" "$D/p" ${GENMODE:-} || { echo "GEN-FAIL $s"; continue; }
  if ! $C "$D/p.w" -o "$D/w" 2>"$D/we"; then
    wfail=$((wfail+1)); echo "WHILE-COMPILE-FAIL seed=$s: $(head -1 $D/we)"; continue
  fi
  wout=$("$D/w" 2>&1); wrc=$?
  if ! cc -O2 -w -o "$D/c" "$D/p.c" 2>/dev/null; then cfail=$((cfail+1)); continue; fi
  cout=$("$D/c" 2>&1)
  if [ "$wrc" -ne 0 ]; then
    echo "WHILE-RUNTIME seed=$s rc=$wrc: $wout"; wfail=$((wfail+1)); continue
  fi
  if [ "$wout" != "$cout" ]; then
    diff=$((diff+1)); echo "MISCOMPILE seed=$s"; echo "  W: $wout"; echo "  C: $cout"
    cp "$D/p.w" "$ROOT/stress/csmith_fail_$s.w"; cp "$D/p.c" "$ROOT/stress/csmith_fail_$s.c"
    continue
  fi
  pass=$((pass+1))
  # cert audit: flag any rejection (silently-dropped optimization) on random input
  if [ -n "${CHECKCERT:-}" ]; then
    rc=$($CA "$D/p.w" 2>/dev/null | grep -c "REJECTED")
    [ "$rc" -gt 0 ] && { rej=$((rej+1)); echo "CERT-REJECT seed=$s ($rc)"; cp "$D/p.w" "$ROOT/stress/csmith_certrej_$s.w"; }
  fi
done
echo ""
echo "=== Csmith campaign (seeds $START..$((START+N-1))) ==="
echo "  match:            $pass"
echo "  MISCOMPILE:       $diff"
echo "  while-fail:       $wfail"
echo "  c-fail:           $cfail"
[ -n "${CHECKCERT:-}" ] && echo "  cert-rejections:  $rej"
