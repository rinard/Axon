#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Metamorphic testing campaign. For each float-free seed, apply semantics-
# preserving rewrites (comm / strength / negate) and require every variant to
# produce IDENTICAL output to the seed (and to the C reference, which the seed
# already matches). A divergence means either the optimizer/codegen miscompiled
# the rewritten shape or the certificate checker accepted an unsound transform.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
C="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/compiler"
EMI="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/emi"
SEEDDIR="$ROOT/stress/t"
OUT="$ROOT/stress/meta"; rm -rf "$OUT"; mkdir -p "$OUT"
TMP=$(mktemp -d); trap "rm -rf $TMP" EXIT

seeds=0; skipped=0; variants=0; ok=0; bug=0; cfail=0
for seed in "$SEEDDIR"/int_*.w "$SEEDDIR"/ctl_*.w "$SEEDDIR"/arr_*.w "$SEEDDIR"/opt_*.w; do
  [ -f "$seed" ] || continue
  name=$(basename "$seed" .w)
  if ! $C "$seed" -o "$TMP/seed" 2>/dev/null; then continue; fi
  seedout=$("$TMP/seed" 2>&1)
  seeds=$((seeds+1))
  for mode in comm strength negate hermes; do
    res=$($EMI "$mode" "$seed" "$OUT" 2>&1)
    echo "$res" | grep -q "^skip:" && { skipped=$((skipped+1)); continue; }
    var="$OUT/${name}_${mode}.w"
    [ -f "$var" ] || continue
    variants=$((variants+1))
    if ! $C "$var" -o "$TMP/var" 2>"$TMP/cerr"; then
      cfail=$((cfail+1)); echo "COMPILE-FAIL $mode $name : $(head -1 $TMP/cerr)"; continue
    fi
    varout=$("$TMP/var" 2>&1)
    if [ "$varout" = "$seedout" ]; then
      ok=$((ok+1))
    else
      bug=$((bug+1))
      echo "DIVERGENCE $mode $name"
      echo "  seed: $(echo "$seedout" | tr '\n' ' ' | cut -c1-100)"
      echo "  $mode: $(echo "$varout"  | tr '\n' ' ' | cut -c1-100)"
    fi
  done
done
echo ""
echo "=== Metamorphic campaign ==="
echo "seeds:           $seeds"
echo "skipped (float): $skipped"
echo "variants tested: $variants"
echo "  equivalent:    $ok"
echo "  DIVERGENCE:    $bug"
echo "  compile-fail:  $cfail"
