#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Overnight master fuzzing campaign. Loops over many seeds, mixing strategies, and
# logs only ANOMALIES (miscompiles, compile/runtime failures, soundness holes) to
# stress/overnight.log. Robust: continues past any single error. Portable timeout
# (no coreutils `timeout` on macOS).
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
C="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/compiler"
CM="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/certmutate"
EMI="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/emi"
GEN="$ROOT/stress/csmith_gen.py"
RT="$ROOT/Compiler/runtime.c"
LOG="$ROOT/stress/overnight.log"
D=$(mktemp -d); trap "rm -rf $D" EXIT
MAXSEED="${1:-1000000}"; TMO="${2:-25}"

# Watchdog timeout. The watchdog subshell's stdout/stderr/stdin are detached from
# any inherited pipe, so this is safe inside `$(run_to ...)` command substitution
# (otherwise the substitution would block for the full timeout every call).
run_to() { local s=$1; shift; "$@" & local p=$!
  ( sleep "$s"; kill -9 $p 2>/dev/null ) </dev/null >/dev/null 2>&1 & local t=$!
  wait $p 2>/dev/null; local rc=$?; kill $t 2>/dev/null; wait $t 2>/dev/null; return $rc; }
log() { echo "[$(date '+%H:%M:%S')] $*" | tee -a "$LOG"; }

log "=== overnight campaign start (maxseed=$MAXSEED timeout=${TMO}s) ==="
done=0; miscomp=0; wfail=0; holes=0
s=0
while [ "$s" -lt "$MAXSEED" ]; do
  s=$((s+1))
  mode=""; [ $((s % 3)) -eq 0 ] && mode="boundary"
  python3 "$GEN" "$s" "$D/p" $mode 2>/dev/null || continue
  if ! run_to "$TMO" $C "$D/p.w" -o "$D/w" 2>"$D/we"; then
    # distinguish timeout (too big) from real failure: re-check small marker
    if grep -qiE "error|fail" "$D/we"; then
      wfail=$((wfail+1)); log "WHILE-COMPILE-FAIL seed=$s mode=$mode: $(head -1 $D/we)"
      cp "$D/p.w" "$ROOT/stress/night_wfail_$s.w"
    fi
    continue
  fi
  wout=$(run_to "$TMO" "$D/w" 2>&1); wrc=$?
  cc -O2 -w -o "$D/c" "$D/p.c" 2>/dev/null || continue
  cout=$("$D/c" 2>&1)
  if [ "$wrc" -ne 0 ]; then
    wfail=$((wfail+1)); log "WHILE-RUNTIME seed=$s rc=$wrc mode=$mode"; cp "$D/p.w" "$ROOT/stress/night_rt_$s.w"; continue
  fi
  if [ "$wout" != "$cout" ]; then
    miscomp=$((miscomp+1)); log "*** MISCOMPILE seed=$s mode=$mode  W=[$wout] C=[$cout]"
    cp "$D/p.w" "$ROOT/stress/night_miscompile_$s.w"; cp "$D/p.c" "$ROOT/stress/night_miscompile_$s.c"; continue
  fi
  done=$((done+1))
  # every 10th passing program: soundness-mutate its cert (checker must reject all
  # behaviour-changing mutations; an accept whose codegen output diverges = hole)
  if [ $((s % 10)) -eq 0 ]; then
    rm -f "$D"/*.s
    out=$(run_to "$TMO" $CM "$D/p.w" "$D" 2>/dev/null)
    if echo "$out" | grep -q '^ACCEPT'; then
      [ -f "$D/correct.s" ] && cc -o "$D/cor" "$D/correct.s" "$RT" 2>/dev/null && O=$("$D/cor" 2>&1) || O="__nocorrect__"
      while read -r f; do
        [ -f "$D/$f" ] || continue
        cc -o "$D/mm" "$D/$f" "$RT" 2>/dev/null || continue
        Om=$("$D/mm" 2>&1)
        if [ "$Om" != "$O" ] && [ "$O" != "__nocorrect__" ]; then
          holes=$((holes+1)); log "*** SOUNDNESS-HOLE seed=$s $f correct=[$O] mutant=[$Om]"; cp "$D/p.w" "$ROOT/stress/night_hole_$s.w"
        fi
      done <<< "$(echo "$out" | grep -oE 'accept_[a-z]+_[0-9]+\.s')"
    fi
  fi
  # progress heartbeat every 50 seeds
  [ $((s % 50)) -eq 0 ] && log "progress: seed=$s pass=$done miscompile=$miscomp wfail=$wfail holes=$holes"
done
log "=== done: seeds=$s pass=$done MISCOMPILE=$miscomp wfail=$wfail HOLES=$holes ==="
