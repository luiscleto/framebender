#!/usr/bin/env bash
# test/par.sh NEW [REF]: stdout, stderr and exit code of binary NEW against
# REF (default data/tmp/parallel/fb_seq, main's machine) on the batch-boundary
# cases of test/gen_par.py, under -c e and -c w, with -w 1, 50, 10000 and the
# default. REF's results are cached in data/tmp/par/ref (started afresh when
# REF is a different binary).
# Inputs: python3 test/gen_par.py && samtools faidx data/tmp/par/par.fa
cd "$(dirname "$0")/.."
N=$1; R=${2:-data/tmp/parallel/fb_seq}
export BEND_NO_TELEMETRY=1
# The cache belongs to one REF binary: another one starts it afresh.
id=$(md5sum < "$R" | cut -c1-32)
[ "$(cat data/tmp/par/ref.id 2>/dev/null)" = "$id" ] || { rm -rf data/tmp/par/ref; mkdir -p data/tmp/par; echo "$id" > data/tmp/par/ref.id; }
mkdir -p data/tmp/par/ref data/tmp/par/new
bad=0; cnt=0
one() { # name vcf mode [w]
  local tag=$1.$3${4:+.w$4} args=(norm -c $3 ${4:+-w $4} -f data/tmp/par/par.fa $2)
  if [ ! -f data/tmp/par/ref/$tag.code ]; then
    nice -n 19 timeout 900 $R "${args[@]}" > data/tmp/par/ref/$tag.out 2> data/tmp/par/ref/$tag.err; echo $? > data/tmp/par/ref/$tag.code
  fi
  nice -n 19 timeout 900 $N "${args[@]}" > data/tmp/par/new/$tag.out 2> data/tmp/par/new/$tag.err; echo $? > data/tmp/par/new/$tag.code
  cnt=$((cnt+1))
  for k in out err code; do cmp -s data/tmp/par/ref/$tag.$k data/tmp/par/new/$tag.$k || { echo "DIFF $tag.$k"; bad=1; }; done
}
for v in data/tmp/par/*.vcf; do
  n=$(basename $v .vcf)
  for m in e w; do
    for w in "" 1 50 10000; do one $n $v $m $w; done
  done
done
[ $bad = 0 ] && echo "ALL IDENTICAL ($cnt runs)"
