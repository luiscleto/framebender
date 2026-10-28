#!/usr/bin/env bash
# Memory-capped check (used by the phase B agents): at most two bend checks at once (two lock slots),
# each under prlimit --as=4000000000 (4 GB of address space; --verdict: a 4 GB
# memory cap, as the Lean kernel needs more address space) and a timeout, niced. Usage:
#   timeout 1800 test/bcheck.sh <file.bend> [--check-only|--verdict]
# Prints the checker's output (last 40 lines).
cd "$(dirname "$0")/.."
f=$1; mode=${2:---check-only}
export BEND_NO_TELEMETRY=1 PATH="$HOME/.elan/bin:$PATH"
L=data/tmp; mkdir -p "$L"
while true; do
  for slot in 1 2; do
    exec {fd}>"$L/bcheck.$slot.lock"
    if flock -n "$fd"; then
      if [ "$mode" = "--verdict" ]; then
        # The Lean kernel reserves more address space than 4 GB: cap its memory
        # (cgroup) instead of its address space.
        timeout 1800 systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 nice -n 19 bend "$f" "$mode" 2>&1 | tail -40
      else
        prlimit --as=4000000000 timeout 1800 nice -n 19 bend "$f" "$mode" 2>&1 | tail -40
      fi
      st=${PIPESTATUS[0]}
      [ "$st" -gt 1 ] && echo "bcheck: bend exited with $st (out of its 4 GB address space, or the 1800 s timeout)"
      exit 0
    fi
    exec {fd}>&-
  done
  sleep 2
done
