#!/usr/bin/env bash
# test/threads.sh NEW REF [DIR]: --threads N changes nothing (law threads).
# Runs binary NEW with --threads N and binary REF without it, on the same
# command line otherwise, and compares stdout, stderr and exit code, on the
# edge cases, the batch-boundary cases (test/gen_par.py), the generated cases
# (test/gen_edge.py, test/gen_rw.py), chr22 and the scrambled file, under
# -c e and -c w, with the default -w and -w 1. N is 1, 2, 3, 7, 16, 32 or 128,
# placed right after "norm", between the options, or after the VCF path.
# Then: the usage errors of --threads; that the generated C still reads
# BENDRTS (if DIR/fb.c exists); and, on Linux, the most threads seen while
# NEW runs with --threads N (Bend's N workers, plus the driver's helpers: the
# VCF read-ahead, and up to N reference reads while the workers wait).
# Results go to DIR (default data/tmp/threads/t). Inputs as for test/same.sh
# and test/par.sh.
cd "$(dirname "$0")/.."
N=$1; R=$2; D=${3:-data/tmp/threads/t}
export BEND_NO_TELEMETRY=1
mkdir -p $D/ref $D/new
bad=0; cnt=0
NS=(1 2 3 7 16 32 128)
# with N at position p (0: after "norm", 1: after -f FASTA, 2: after the VCF)
cmdline() { # p n mode w fasta vcf
  local p=$1 n=$2 m=$3 w=$4 fa=$5 v=$6 t=(--threads $2)
  case $p in
    0) echo norm "${t[@]}" -c $m ${w:+-w $w} -f $fa $v ;;
    1) echo norm -c $m ${w:+-w $w} -f $fa "${t[@]}" $v ;;
    2) echo norm -c $m ${w:+-w $w} -f $fa $v "${t[@]}" ;;
  esac
}
one() { # name fasta vcf mode [w]
  local tag=$1.$4${5:+.w$5} fa=$2 v=$3 m=$4 w=$5
  if [ ! -f $D/ref/$tag.code ]; then
    nice -n 19 timeout 900 $R norm -c $m ${w:+-w $w} -f $fa $v > $D/ref/$tag.out 2> $D/ref/$tag.err; echo $? > $D/ref/$tag.code
  fi
  local i=0
  for n in "${NS[@]}"; do
    local p=$((i % 3)); i=$((i + 1))
    nice -n 19 timeout 900 $N $(cmdline $p $n $m "$w" $fa $v) > $D/new/$tag.out 2> $D/new/$tag.err; echo $? > $D/new/$tag.code
    cnt=$((cnt+1))
    for k in out err code; do cmp -s $D/ref/$tag.$k $D/new/$tag.$k || { echo "DIFF $tag.$k (--threads $n at $p)"; bad=1; }; done
  done
}
for m in e w; do
  for w in "" 1; do
    for v in test/edge/*.vcf; do one edge_$(basename $v .vcf) test/edge/ref.fa $v $m $w; done
    for v in data/tmp/par/*.vcf; do one par_$(basename $v .vcf) data/tmp/par/par.fa $v $m $w; done
    for v in data/tmp/edge2/*.vcf; do one e2_$(basename $v .vcf) data/chr22.fa $v $m $w; done
    for v in data/tmp/rw/in/*.vcf; do
      n=$(basename $v .vcf); fa=data/tmp/rw/rw.fa; [ $n = scr2 ] && fa=data/chr22.fa
      one rw_$n $fa $v $m $w
    done
    one chr22 data/chr22.fa data/hg002.chr22.vcf $m $w
    one scr data/chr22.fa data/scr.vcf $m $w
  done
done
[ $bad = 0 ] && echo "ALL IDENTICAL ($cnt runs)"

# Usage errors: exit 2 and the usage line, as with any refused command line.
u=0
for a in "--threads 0" "--threads 129" "--threads 1000000" "--threads x" "--threads -1" "--threads" "--threads 0 --threads 8" "-c --threads 8" "-w --threads 8"; do
  $N norm -f data/chr22.fa data/hg002.chr22.vcf $a > $D/u.out 2> $D/u.err; c=$?
  if [ $c != 2 ] || [ -s $D/u.out ] || ! grep -q '^usage: framebender norm' $D/u.err; then echo "USAGE? [$a] exit $c"; u=1; fi
done
[ $u = 0 ] && echo "USAGE ERRORS OK"

if [ -f $D/fb.c ]; then
  grep -q 'getenv("BENDRTS")' $D/fb.c && echo "BENDRTS READ" || echo "BENDRTS NOT READ: the constructor in io64.c does nothing"
fi

# The thread count (Linux): the most threads seen while NEW runs on chr22.
if [ -d /proc/self/task ]; then
  for n in 1 3 8; do
    $N norm --threads $n -f data/chr22.fa data/hg002.chr22.vcf > /dev/null 2>&1 & pid=$!
    mx=0
    while kill -0 $pid 2>/dev/null; do
      k=$(ls /proc/$pid/task 2>/dev/null | wc -l); [ "$k" -gt $mx ] && mx=$k
    done
    wait $pid
    echo "--threads $n: at most $mx threads seen"
  done
fi
