#!/usr/bin/env bash
# Memory-capped check (used by the phase B agents): at most two bend checks at once (two lock slots),
# each under a 4 GB memory cap (a cgroup: MemoryMax=4G, no swap) and a timeout, niced, with a
# 64 MB stack (phase E: the largest proofs overflowed bend's machine stack, at random, with the
# default 16 MB; an address-space cap leaves no room for 64 MB thread stacks). Usage:
#   timeout 1800 test/bcheck.sh <file.bend> [--check-only|--verdict]
# Prints the checker's output (last 40 lines).
cd "$(dirname "$0")/.."
ulimit -s 65536
f=$1; mode=${2:---check-only}
export BEND_NO_TELEMETRY=1 PATH="$HOME/.elan/bin:$PATH"
L=data/tmp; mkdir -p "$L"
while true; do
  for slot in 1 2; do
    exec {fd}>"$L/bcheck.$slot.lock"
    if flock -n "$fd"; then
      timeout 1800 systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 nice -n 19 bend "$f" "$mode" 2>&1 | tail -40
      st=${PIPESTATUS[0]}
      [ "$st" -gt 1 ] && echo "bcheck: bend exited with $st (over its 4 GB memory cap, or the 1800 s timeout)"
      exit 0
    fi
    exec {fd}>&-
  done
  sleep 2
done
