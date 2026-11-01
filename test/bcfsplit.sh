#!/usr/bin/env bash
# test/bcfsplit.sh REF IN.vcf.gz OUT [norm options]: bcftools norm split the usual way to use
# more cores, one job per chromosome, JOBS at a time (default 16), then joined in the input's
# order. Each job is `bcftools norm -f REF -r CHROM [norm options]` on the indexed input (a .csi
# or .tbi must exist: `bcftools index IN`); the chromosomes are those the index lists. On an
# input with one chromosome, set REGIONS=N to split it instead into N equal stretches from its
# first record to its end (`--regions-overlap pos`: each record goes to the stretch holding its
# POS). OUT ending in .vcf.gz: the jobs write -Oz, joined by `bcftools concat --naive` (no
# recompression); a -W among the options indexes OUT once it is joined (`bcftools index`, CSI).
# Otherwise the jobs write plain VCF, joined by plain concatenation: the first job's header, then
# every job's records. The jobs' files go in OUT.parts/, removed at the end. Prints the time of
# the jobs and of the join on stderr. Set BCFTOOLS to choose the binary.
set -eo pipefail
BC=${BCFTOOLS:-bcftools}; J=${JOBS:-16}
F=$1; V=$2; O=$3; shift 3
W=(); opts=()
for a in "$@"; do case $a in -W|--write-index) W=(-W) ;; *) opts+=("$a") ;; esac; done
P=$O.parts; rm -rf "$P"; mkdir -p "$P"
case $O in *.vcf.gz) ext=vcf.gz; fmt=-Oz ;; *) ext=vcf; fmt=-Ov ;; esac
if [ -n "$REGIONS" ]; then
  c=$("$BC" index -s "$V" | cut -f1)
  [ "$(echo "$c" | wc -l)" = 1 ] || { echo "bcfsplit: REGIONS needs one chromosome" >&2; exit 1; }
  len=$("$BC" view -h "$V" | sed -n "s/^##contig=<ID=$c,.*length=\([0-9]*\).*/\1/p")
  beg=$({ "$BC" view -H "$V" || :; } | head -1 | cut -f2)
  step=$(( (len - beg) / REGIONS + 1 ))
  rs=$(for i in $(seq 0 $((REGIONS - 1))); do
    echo "$c:$((beg + i * step))-$((beg + (i + 1) * step - 1))"; done)
  ov=(--regions-overlap pos)
else
  rs=$("$BC" index -s "$V" | cut -f1); ov=()
fi
job() {
  "$BC" norm -f "$F" -r "$2" "${ov[@]}" "${opts[@]}" $fmt -o "$P/$1.$ext" "$V" 2> "$P/$1.err" ||
    echo "$2" >> "$P/failed"
}
t0=$EPOCHREALTIME; i=0
for r in $rs; do
  while [ "$(jobs -rp | wc -l)" -ge "$J" ]; do wait -n; done
  i=$((i + 1)); job "$(printf %04d $i)" "$r" &
done
wait; t1=$EPOCHREALTIME
[ ! -e "$P/failed" ] ||
  { cat "$P"/*.err >&2; echo "bcfsplit: failed: $(cat "$P/failed")" >&2; exit 1; }
if [ $ext = vcf.gz ]; then
  "$BC" concat --naive -o "$O" "$P"/*.vcf.gz
  [ -z "$W" ] || "$BC" index --threads "$J" "$O"
else
  ps=("$P"/*.vcf); h=$(grep -m1 -n '^#CHROM' "${ps[0]}" | cut -d: -f1)
  { cat "${ps[0]}"; for p in "${ps[@]:1}"; do tail -n +$((h + 1)) "$p"; done; } > "$O"
fi
rm -rf "$P"
awk -v a="$t0" -v b="$t1" -v c="$EPOCHREALTIME" -v n=$i \
  'BEGIN{printf "bcfsplit: %d jobs %.2f s, join %.2f s\n", n, b-a, c-b}' >&2
