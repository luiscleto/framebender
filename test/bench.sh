#!/usr/bin/env bash
# test/bench.sh REF VCF [ROUNDS] [-- options for both tools]: time framebender against bcftools
# norm, interleaved, ROUNDS rounds (default 3), all with -c w, writing to a file. Each round runs
# these ways (WAYS chooses some, e.g. WAYS="fb bc"):
#   fb       framebender, default (16 pieces at a time)
#   fb1      framebender --threads 1
#   bc       bcftools norm (one thread)
#   bcsplit  bcftools norm per chromosome, 16 jobs at a time, joined (test/bcfsplit.sh): only on
#            an indexed .vcf.gz; REGIONS=N splits a one-chromosome file into N stretches instead
#   bc16     bcftools norm --threads 16 (threads compress output; they do not normalize)
# Prints one line per run: way, wall seconds, CPU seconds (user + system), peak memory (MB), exit
# code, and the first 12 hex digits of the md5 of the output's records (its lines not starting
# with #: the header differs, bcftools' records the date). Peak memory is the peak resident size:
# of the process, or for bcsplit the largest sum over its processes, sampled every 10 ms.
# The output is OUTDIR/out.vcf (out.vcf.gz when the options hold -Oz), OUTDIR by default
# data/tmp/bench in this checkout. Put it on a disk, not on a tmpfs such as /tmp on many Linux
# systems: writing to memory is faster, and changes the comparison. It is deleted before each run,
# followed by a sync and 2 s of rest; it needs room for one output (bcsplit: two).
# Each run is under nice -n 19 and timeout TIMEOUT (default 600 s). Set FRAMEBENDER and BCFTOOLS
# to choose the binaries, CPUS to pin every run (taskset -c CPUS; the README's runs use CPUS=0-15,
# the performance cores of a hybrid CPU), and MEMMAX to cap each run's memory (systemd-run --user
# --scope -p MemoryMax=MEMMAX -p MemorySwapMax=0; the README's runs use MEMMAX=12G). The input and
# the reference are read once before the first round, so that no run starts with a cold cache.
# CHECK, if set, is a command run before each round: when it fails, the benchmark stops (the
# README's runs check that the laptop is on AC power, in the balanced profile).
cd "$(dirname "$0")/.."
F=$1; V=$2; N=3; shift 2
[ $# -gt 0 ] && [ "$1" != -- ] && { N=$1; shift; }
[ "$1" = -- ] && shift
FB=${FRAMEBENDER:-./framebender}; BC=${BCFTOOLS:-bcftools}
D=${OUTDIR:-data/tmp/bench}; mkdir -p "$D"
O=$D/out.vcf; case " $* " in *" -Oz"*) O=$D/out.vcf.gz ;; esac
export BEND_NO_TELEMETRY=1 BCFTOOLS=$BC
pre=(nice -n 19 timeout "${TIMEOUT:-600}")
[ -n "$CPUS" ] && pre+=(taskset -c "$CPUS")
cap=()
[ -n "$MEMMAX" ] && cap=(systemd-run --user --scope -q -p MemoryMax="$MEMMAX" -p MemorySwapMax=0)
run() {
  local l=$1; shift
  rm -f "$O" "$O".csi "$O".tbi
  local r=$("${cap[@]}" python3 -I -c '
import os, resource, subprocess, sys, threading, time
def tree(pid):
    ps, i = [pid], 0
    while i < len(ps):
        try:
            for t in os.listdir(f"/proc/{ps[i]}/task"):
                with open(f"/proc/{ps[i]}/task/{t}/children") as f: ps += map(int, f.read().split())
        except OSError: pass
        i += 1
    return ps
def rss(ps):
    s = 0
    for p in ps:
        try:
            with open(f"/proc/{p}/statm") as f: s += int(f.read().split()[1])
        except OSError: pass
    return s * os.sysconf("SC_PAGE_SIZE")
os.sync(); time.sleep(2)
peak, done = 0, False
with open(sys.argv[1], "wb") as err:
    t0 = time.perf_counter()
    p = subprocess.Popen(sys.argv[2:], stdout=subprocess.DEVNULL, stderr=err)
    def sample():
        global peak
        while not done: peak = max(peak, rss(tree(p.pid))); time.sleep(0.01)
    s = threading.Thread(target=sample); s.start()
    p.wait()
    t1 = time.perf_counter(); done = True; s.join()
r = resource.getrusage(resource.RUSAGE_CHILDREN)
mb = max(peak / 2**20, r.ru_maxrss / 1024)
print(f"{t1 - t0:.2f} s cpu {r.ru_utime + r.ru_stime:.2f} s {mb:.0f} MB exit {p.returncode}")
' "$D/err.$l" "${pre[@]}" "$@")
  echo "$l $r $(zcat -f "$O" 2>/dev/null | grep -v '^#' | md5sum | cut -c1-12)" \
    "$(grep -h '^bcfsplit:' "$D/err.$l" 2>/dev/null)"
  rm -f "$O" "$O".csi "$O".tbi
}
ways=${WAYS:-fb fb1 bc bcsplit}
case $V in
  *.vcf.gz) [ -e "$V.csi" ] || [ -e "$V.tbi" ] || ways=${ways/bcsplit/} ;;
  *) ways=${ways/bcsplit/} ;;
esac
cat "$V" "$F" "$F".fai > /dev/null
for i in $(seq "$N"); do
  [ -z "$CHECK" ] || $CHECK || { echo "round $i: CHECK failed: $CHECK"; exit 1; }
  for w in $ways; do case $w in
    fb) run fb "$FB" norm -c w "$@" -f "$F" -o "$O" "$V" ;;
    fb1) run fb1 "$FB" norm -c w --threads 1 "$@" -f "$F" -o "$O" "$V" ;;
    bc) run bc "$BC" norm -c w "$@" -f "$F" -o "$O" "$V" ;;
    bc16) run bc16 "$BC" norm -c w --threads 16 "$@" -f "$F" -o "$O" "$V" ;;
    bcsplit) run bcsplit test/bcfsplit.sh "$F" "$V" "$O" -c w "$@" ;;
  esac; done
done
