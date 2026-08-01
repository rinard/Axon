#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Portable per-command timeout. macOS ships no `timeout`/`gtimeout`/`setsid`, so this uses a
# background job + a sleep-watchdog that kills it (the same trick certfuzz.sh uses inline).
#
# Usage:  run_to.sh SECONDS cmd [args...]
# Exit:   the command's exit code, or 124 if it was killed for running past SECONDS.
#
# Use it to guard anything that can loop or be pathologically slow on adversarial input — the
# optimizer passes and the certificate checker (via compiler / certaudit / certmutate), and any
# compiled program you run. A timeout is a candidate non-termination / pathological-slowness
# finding, not a failure to retry.
s="$1"; shift
case "$s" in ''|*[!0-9]*) echo "usage: run_to.sh SECONDS cmd [args...]" >&2; exit 2;; esac
[ "$#" -gt 0 ] || { echo "usage: run_to.sh SECONDS cmd [args...]" >&2; exit 2; }

"$@" & p=$!
( sleep "$s"; kill -9 "$p" 2>/dev/null ) >/dev/null 2>&1 & w=$!
wait "$p" 2>/dev/null; rc=$?
kill "$w" 2>/dev/null; wait "$w" 2>/dev/null
[ "$rc" -ge 128 ] && rc=124      # killed by a signal (the watchdog) → report as timeout
exit "$rc"
