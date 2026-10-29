#!/usr/bin/env bash
# test/bench.sh REF VCF [ROUNDS] [-- extra framebender options]: time framebender against
# bcftools norm, interleaved, ROUNDS rounds (default 3), both with -c w, writing to a file.
# Prints one line per run: tool, wall seconds, peak memory (MB), exit code, and the first 12
# hex digits of the output's md5 (framebender's should be the same in every run; bcftools'
# changes, as its header records the date). The output goes to $TMPDIR (default /tmp),
# deleted before each run, followed by a sync and 2 s of rest; it needs room for one output.
# Set FRAMEBENDER and BCFTOOLS to choose the binaries, and CPUS to pin both (taskset -c CPUS;
# the README's runs use CPUS=0-15, the performance cores of a hybrid CPU). Runs under
# nice -n 19 with a 600 s timeout per run.
cd "$(dirname "$0")/.."
F=$1; V=$2; N=3; shift 2
[ $# -gt 0 ] && [ "$1" != -- ] && { N=$1; shift; }
[ "$1" = -- ] && shift
FB=${FRAMEBENDER:-./framebender}; BC=${BCFTOOLS:-bcftools}
O=${TMPDIR:-/tmp}/framebender_bench.$$.out
export BEND_NO_TELEMETRY=1
pin=(); [ -n "$CPUS" ] && pin=(taskset -c "$CPUS")
run() {
  local l=$1; shift
  local r=$(python3 -I -c '
import os, resource, subprocess, sys, time
out = sys.argv[1]
if os.path.exists(out): os.remove(out)
os.sync(); time.sleep(2)
with open(out, "wb") as f:
    t0 = time.perf_counter()
    p = subprocess.run(sys.argv[2:], stdout=f, stderr=subprocess.DEVNULL)
    t1 = time.perf_counter()
r = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"{t1 - t0:.2f} s {r.ru_maxrss / 1024:.0f} MB exit {p.returncode}")
' "$O" nice -n 19 timeout 600 "${pin[@]}" "$@")
  echo "$l $r $(md5sum < "$O" | cut -c1-12)"
  rm -f "$O"
}
for i in $(seq "$N"); do
  run framebender "$FB" norm -c w "$@" -f "$F" "$V"
  run bcftools "$BC" norm -c w -f "$F" "$V"
done
