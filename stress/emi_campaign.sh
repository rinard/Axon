#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# EMI (Orion/Athena) campaign. For each float-free seed:
#   - generate orion + athena mutants (mutate dead regions),
#   - compile & run seed and every mutant,
#   - every mutant MUST produce identical output to the seed (dead code never runs).
# Divergence — especially the sentinel [EMILEAK] appearing — is a compiler bug.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
C="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/compiler"
EMI="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/emi"
SEEDDIR="$ROOT/stress/t"
OUT="$ROOT/stress/emi"; rm -rf "$OUT"; mkdir -p "$OUT"
TMP=$(mktemp -d); trap "rm -rf $TMP" EXIT

seeds=0; skipped=0; mutants=0; ok=0; bug=0; cfail=0; nodead=0
for seed in "$SEEDDIR"/int_*.w "$SEEDDIR"/ctl_*.w "$SEEDDIR"/arr_*.w "$SEEDDIR"/opt_*.w; do
  [ -f "$seed" ] || continue
  name=$(basename "$seed" .w)
  # seed output
  if ! $C "$seed" -o "$TMP/seed" 2>/dev/null; then continue; fi
  seedout=$("$TMP/seed" 2>&1)
  seeds=$((seeds+1))
  for mode in orion athena; do
    res=$($EMI "$mode" "$seed" "$OUT" 2>&1)
    if echo "$res" | grep -q "^skip:"; then skipped=$((skipped+1)); continue; fi
    nd=$(echo "$res" | grep -oE "dead arms: [0-9]+" | grep -oE "[0-9]+")
    [ "${nd:-0}" = "0" ] && { nodead=$((nodead+1)); continue; }
    mut="$OUT/${name}_${mode}_all.w"
    [ -f "$mut" ] || continue
    mutants=$((mutants+1))
    if ! $C "$mut" -o "$TMP/mut" 2>"$TMP/cerr"; then
      cfail=$((cfail+1)); echo "COMPILE-FAIL $mode $name : $(head -1 $TMP/cerr)"; continue
    fi
    mutout=$("$TMP/mut" 2>&1)
    if [ "$mutout" = "$seedout" ]; then
      ok=$((ok+1))
    else
      bug=$((bug+1))
      echo "DIVERGENCE $mode $name"
      echo "  seed: $(echo "$seedout" | tr '\n' ' ')"
      echo "  mut : $(echo "$mutout"  | tr '\n' ' ')"
      echo "$mutout" | grep -q EMILEAK && echo "  >>> [EMILEAK] sentinel executed — dead code ran!"
    fi
  done
done
echo ""
echo "=== EMI campaign ==="
echo "seeds tried:        $seeds"
echo "skipped (float):    $skipped"
echo "no dead arms:       $nodead"
echo "mutants tested:     $mutants"
echo "  equivalent (ok):  $ok"
echo "  DIVERGENCE (bug): $bug"
echo "  compile-fail:     $cfail"
