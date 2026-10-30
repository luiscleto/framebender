#!/usr/bin/env bash
# test/same.sh NEW [REF]: stdout, stderr and exit code of binary NEW
# against REF (default data/tmp/fb_ref, main's build) on every phase C case.
# REF's results are cached in data/tmp/rw/ref (started afresh when REF is
# a different binary).
# Inputs: run `python3 test/gen_edge.py` and `python3 test/gen_rw.py` first, from
# the repository root (they write data/tmp/edge2 and data/tmp/rw).
cd "$(dirname "$0")/.."
N=$1; R=${2:-data/tmp/fb_ref}
export BEND_NO_TELEMETRY=1
# The cache belongs to one REF binary: another one starts it afresh.
id=$(md5sum < "$R" | cut -c1-32)
[ "$(cat data/tmp/rw/ref.id 2>/dev/null)" = "$id" ] || { rm -rf data/tmp/rw/ref; mkdir -p data/tmp/rw; echo "$id" > data/tmp/rw/ref.id; }
mkdir -p data/tmp/rw/ref data/tmp/rw/new
bad=0; cnt=0
one() { # name fasta vcf mode [w]
  local tag=$1.$4${5:+.w$5} args=(norm -c $4 ${5:+-w $5} -f $2 $3)
  if [ ! -f data/tmp/rw/ref/$tag.code ]; then
    nice -n 19 timeout 900 $R "${args[@]}" > data/tmp/rw/ref/$tag.out 2> data/tmp/rw/ref/$tag.err; echo $? > data/tmp/rw/ref/$tag.code
  fi
  nice -n 19 timeout 900 $N "${args[@]}" > data/tmp/rw/new/$tag.out 2> data/tmp/rw/new/$tag.err; echo $? > data/tmp/rw/new/$tag.code
  cnt=$((cnt+1))
  for k in out err code; do cmp -s data/tmp/rw/ref/$tag.$k data/tmp/rw/new/$tag.$k || { echo "DIFF $tag.$k"; bad=1; }; done
}
for m in e w; do
  for v in test/edge/*.vcf; do one edge_$(basename $v .vcf) test/edge/ref.fa $v $m; done
  one chr22 data/chr22.fa data/hg002.chr22.vcf $m
  one scr data/chr22.fa data/scr.vcf $m
  for v in data/tmp/edge2/*.vcf; do one e2_$(basename $v .vcf) data/chr22.fa $v $m; done
  for v in data/tmp/rw/in/*.vcf; do
    n=$(basename $v .vcf); fa=data/tmp/rw/rw.fa; [ $n = scr2 ] && fa=data/chr22.fa
    one rw_$n $fa $v $m
  done
  for w in 1 5 300; do
    one scr data/chr22.fa data/scr.vcf $m $w
    one scr2 data/chr22.fa data/tmp/rw/in/scr2.vcf $m $w
    one e2_unsorted data/chr22.fa data/tmp/edge2/unsorted.vcf $m $w
    one e2_mix_crlf data/chr22.fa data/tmp/edge2/mix_crlf.vcf $m $w
    for n in mix multi chroms far crlf; do one rw_$n data/tmp/rw/rw.fa data/tmp/rw/in/$n.vcf $m $w; done
  done
done
[ $bad = 0 ] && echo "ALL IDENTICAL ($cnt runs)"
