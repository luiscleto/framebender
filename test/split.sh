#!/usr/bin/env bash
# test/split.sh NEW [SEEDS] [DIR]: -m against bcftools 1.24 on the random
# well-formed multiallelic files of test/gen_split.py (seeds 1..SEEDS, default
# 40), each with -c w -m -any and with -c w -m -any --multi-overlaps .
# Records are compared as test/compare.sh does (REF and ALT upper-cased,
# sample columns padded to the FORMAT length), and a sample value that is
# only missing values (bcftools writes a missing Number=R value as .,.) read
# as one '.'. Exits 0 when every run has the same exit code and the same
# records.
cd "$(dirname "$0")/.."
N=$(realpath "$1"); S=${2:-40}; D=${3:-data/tmp/split_t}
BC=${BCFTOOLS:-bcftools}
mkdir -p $D; bad=0; runs=0
up() { grep -v '^#' "$1" | awk -F'\t' 'BEGIN{OFS="\t"}{$4=toupper($4);$5=toupper($5)
  k=split($9,a,":"); for(i=10;i<=NF;i++){n=split($i,b,":"); while(n<k){b[++n]="."}
    v=""; for(j=1;j<=n;j++){if(b[j] ~ /^\.(,\.)+$/) b[j]="."; v=v (j>1?":":"") b[j]}; $i=v}; print}'; }
for s in $(seq 1 $S); do
  python3 test/gen_split.py $D $s
  samtools faidx $D/s$s.fa 2> /dev/null || rm -f $D/s$s.fa.fai
  for o in "" "--multi-overlaps ."; do
    nice -n 19 timeout 600 $N norm -c w -m -any $o -f $D/s$s.fa $D/s$s.vcf > $D/fb.vcf 2> $D/fb.err; fe=$?
    nice -n 19 timeout 600 $BC norm --no-version -c w -m -any $o -f $D/s$s.fa $D/s$s.vcf > $D/bc.vcf 2> $D/bc.err; be=$?
    runs=$((runs + 1))
    n=$(diff <(up $D/fb.vcf) <(up $D/bc.vcf) | grep -c '^<')
    if [ $fe != $be ] || [ $n != 0 ]; then
      bad=1; echo "DIFF seed $s [$o]: exit framebender $fe bcftools $be, $n records differ"
      diff <(up $D/fb.vcf) <(up $D/bc.vcf) | cut -c1-200 | head -6
    fi
  done
done
rm -f $D/fb.vcf $D/bc.vcf $D/fb.err $D/bc.err
[ $bad = 0 ] && echo "ALL $runs RUNS THE SAME AS BCFTOOLS"
exit $bad
