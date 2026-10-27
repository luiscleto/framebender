#!/usr/bin/env bash
# Differential comparison with bcftools 1.24 (decision R21): runs both tools
# with -c w and reports differences in the records and the exit codes.
# Records are compared after upper-casing REF/ALT (bcftools keeps lower case) and
# padding sample columns to the FORMAT length with '.' (htslib does on output).
# Large inputs: TMPDIR on a disk with room for both outputs.
# Usage: test/compare.sh ref.fa in.vcf
set -u
BC=${BCFTOOLS:-$HOME/.local/opt/htslib-1.24/bin/bcftools}
FB=${FRAMEBENDER:-$(dirname "$0")/../framebender}
ref=$1; vcf=$2
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
nice -n 19 timeout 3600 "$FB" norm -c w -f "$ref" "$vcf" > "$tmp/fb.vcf" 2> "$tmp/fb.err"; fe=$?
nice -n 19 timeout 3600 "$BC" norm -c w -f "$ref" "$vcf" > "$tmp/bc.vcf" 2> "$tmp/bc.err"; be=$?
up() { grep -v '^#' "$1" | awk -F'\t' 'BEGIN{OFS="\t"}{$4=toupper($4);$5=toupper($5)
  k=split($9,a,":"); for(i=10;i<=NF;i++){n=split($i,b,":"); while(n<k){$i=$i":.";n++}}; print}'; }
n=$(diff <(up "$tmp/fb.vcf") <(up "$tmp/bc.vcf") | grep -c '^<')
echo "exit codes: framebender $fe, bcftools $be; differing records: $n"
diff <(up "$tmp/fb.vcf") <(up "$tmp/bc.vcf") | cut -c1-160 | head -20
