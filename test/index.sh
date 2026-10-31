#!/usr/bin/env bash
# test/index.sh NEW [DIR]: the index option -W (laws index and index_sink) and
# the driver's index writer, on binary NEW. Results go to DIR (default
# data/tmp/index/t). Needs tabix and bcftools (htslib 1.24, with libdeflate,
# for the byte-identity checks), cc, python3 and timeout.
#
# 1. The differential rule, per format: on the edge cases, the
#    batch-boundary cases (test/gen_par.py), the generated cases
#    (test/gen_edge.py, test/gen_rw.py), chr22, the scrambled file,
#    test/gen_out.py's block-cut cases and test/gen_index.py's index cases,
#    under -c e and -c w, the run without -W comes first (its output a BGZF
#    -o file at a level that turns with the case). If its code is not 0, each
#    -W run must be that run exactly (stdout, stderr, code, output bytes) with
#    no index. Otherwise CSI is judged by bcftools index and TBI by tabix -p
#    vcf, each on its own: if the tool refuses the output, the -W run gives
#    the same stdout and stderr, then "error: cannot index <path>", exit 2,
#    the output less its end-of-file block, and no index; else the same
#    report and output, and the tool's index bytes. Each case runs once with
#    CSI and once with TBI; each -W run turns its spelling (within its
#    format: five for CSI, three for TBI), its place in the line (three),
#    --threads N (1, 2, 3, 7, 16, 32, 128) and the -o form (.vcf.gz, -Ov with .vcf.gz,
#    .vcf.bgz, .VCF.GZ), and starts with an old index at both names: one must
#    be the new index, the other gone, and no .tmp or .old file left. chr22
#    and the scrambled file also at every level of z, z0, z1, z9; with -m
#    (-c w -m -any, and -c e -m -both on the edge cases), chr22, the
#    scrambled file and the edge cases again. With
#    PIECES="BIN ...", the same -W runs on each binary BIN (the small-piece
#    builds) for the small cases; with BIG=1, the 1000 Genomes slice, its
#    chr22 and the whole genome.
# 2. Queries: tabix on chr22's index, against bcftools view of a copy indexed
#    by bcftools index, and against the records by POS, for regions at block
#    and 16 kb bin boundaries.
# 3. Files: the order at the open and the close by failure injection
#    (test/fi_shim.c), each step and each index name, for CSI and TBI; -o
#    paths htslib could read as URLs; a FIFO with no reader (under a
#    timeout), with a reader, /dev/null; index names that are the -o file or
#    an input (a symlink, a hard link, stderr's file); index names that are
#    directories (themselves, or through a symlink); an older <stem>.csi
#    that htslib reads before the .tbi; an existing <name>.old; BadIdx; a
#    driver error and Bend's runtime stopping after the open; a taken
#    temporary name; the new index's mode and mtime; a run without -W after
#    one with it.
# 4. Builds: with NOHTS=binary (FB_NO_HTSLIB=1 ./build.sh) "no index in this
#    build"; with PLAIN=binary (bend main.bend -o) "no BGZF in this build";
#    build.sh's refusals of a libcurl htslib and of none; tools/build_htslib.sh
#    with a wrong tarball (SKIPBUILD=1 skips these two).
# 5. Usage errors. 6. The threads seen with each -W spelling.
# Exits 0 when all pass. QUICK=1 skips the identity runs of 1.
cd "$(dirname "$0")/.."
R0=$(pwd)
N=$(realpath "$1"); D=${2:-data/tmp/index/t}
export BEND_NO_TELEMETRY=1
id=$(md5sum < "$N" | cut -c1-32)
[ "$(cat $D/ref.id 2>/dev/null)" = "$id" ] || { rm -rf $D/ref; mkdir -p $D; echo "$id" > $D/ref.id; }
rm -rf $D/new $D/f; mkdir -p $D/ref $D/new $D/gen $D/gi $D/f
EOF28=1f8b08040000000000ff0600424302001b0003000000000000000000
bad=0; cnt=0
NS=(1 2 3 7 16 32 128)
SP=(-W -Wtbi -Wcsi -W=tbi -W=csi --write-index=tbi --write-index --write-index=csi)
SPC=(-W -Wcsi -W=csi --write-index --write-index=csi)
SPT=(-Wtbi -W=tbi --write-index=tbi)
fail() { echo "FAIL $*"; bad=1; }
eofhex() { tail -c 28 "$1" | od -An -tx1 | tr -d ' \n'; }
fmt_of() { case $1 in *tbi) echo tbi ;; *) echo csi ;; esac; }

# The run without -W of $tag at level $lv, and each tool on a copy of its
# output: $D/ref/$tag.$lv.{out,err,code,vcf.gz}, .{csi,tbi}.ok (the tool's
# exit code) and the tool's index.
ref() { # tag fasta vcf mode level
  local r=$D/ref/$1.$5
  [ -f $r.code ] && return
  nice -n 19 timeout 900 $N norm -c $4 -O$5 -o $r.vcf.gz -f $2 $3 > $r.out 2> $r.err; echo $? > $r.code
  [ -e $r.vcf.gz ] || : > $r.vcf.gz
  cp $r.vcf.gz $r.c.vcf.gz; bcftools index $r.c.vcf.gz 2> /dev/null; echo $? > $r.csi.ok
  mv -f $r.c.vcf.gz.csi $r.csi 2> /dev/null
  cp $r.vcf.gz $r.t.vcf.gz; tabix -p vcf $r.t.vcf.gz 2> /dev/null; echo $? > $r.tbi.ok
  mv -f $r.t.vcf.gz.tbi $r.tbi 2> /dev/null
  rm -f $r.c.vcf.gz $r.t.vcf.gz
}

# One -W run of $tag for format f (csi or tbi), judged by the rule above.
k=0; kc=0; kt=0
wrun() { # bin tag fasta vcf mode level f
  local B=$1 tag=$2 fa=$3 v=$4 m=$5 lv=$6 f=$7 w
  if [ $f = csi ]; then w=${SPC[$((kc % 5))]}; kc=$((kc + 1)); else w=${SPT[$((kt % 3))]}; kt=$((kt + 1)); fi
  local n=${NS[$((k % 7))]} p=$((k % 3)) form=$((k % 4)); k=$((k + 1))
  local o=$D/new/$tag opts
  case $form in
    0) o=$o.vcf.gz; opts="-O$lv -o $o" ;;
    1) o=$o.vcf.gz; lv=z; opts="-Ov -o $o" ;;
    2) o=$o.vcf.bgz; opts="-O$lv -o $o" ;;
    3) o=$o.VCF.GZ; opts="-O$lv -o $o" ;;
  esac
  ref $tag $fa $v "$m" $lv
  local r=$D/ref/$tag.$lv code=$(cat $D/ref/$tag.$lv.code) other=tbi
  [ $f = tbi ] && other=csi
  rm -f $o $o.*; printf 'old csi\n' > $o.csi; printf 'old tbi\n' > $o.tbi
  local a="--threads $n $opts $w"
  case $p in
    0) set -- norm $a -c $m -f $fa $v ;;
    1) set -- norm -c $m -f $fa $a $v ;;
    2) set -- norm -c $m -f $fa $v $a ;;
  esac
  nice -n 19 timeout 900 $B "$@" > $D/new/$tag.out 2> $D/new/$tag.err; local c=$?
  cnt=$((cnt + 1))
  local x="$tag [$*]"
  ls $o.*tmp* $o.*.old* > /dev/null 2>&1 && fail "$x: a .tmp or .old file left"
  if [ $code != 0 ]; then
    [ $c = $code ] && cmp -s $D/new/$tag.err $r.err && cmp -s $D/new/$tag.out $r.out && cmp -s $o $r.vcf.gz || fail "$x: not the run without -W (code $code)"
    [ -e $o.csi ] || [ -e $o.tbi ] && fail "$x: an index after code $code"
  elif [ "$(cat $r.$f.ok)" != 0 ]; then
    { cat $r.err; echo "error: cannot index $o"; } > $D/new/$tag.want
    [ $c = 2 ] && cmp -s $D/new/$tag.err $D/new/$tag.want && cmp -s $D/new/$tag.out $r.out || fail "$x: not 'cannot index' after the run's messages (exit $c)"
    cmp -s $o <(head -c -28 $r.vcf.gz) || fail "$x: not the output less its end-of-file block"
    [ -e $o.csi ] || [ -e $o.tbi ] && fail "$x: an index after cannot index"
    echo "refused" > $D/new/$tag.$f.refused
  else
    [ $c = 0 ] && cmp -s $D/new/$tag.err $r.err && cmp -s $D/new/$tag.out $r.out && cmp -s $o $r.vcf.gz || fail "$x: report or output not the run without -W (exit $c)"
    cmp -s $o.$f $r.$f || fail "$x: the $f is not the tool's"
    [ -e $o.$other ] && fail "$x: the old .$other is still there"
  fi
}

LVS=(z z0 z1 z9)
lk=0
one() { # bin name fasta vcf mode
  local lv=${LVS[$((lk % 4))]}; lk=$((lk + 1))
  wrun $1 $2.$5 $3 $4 $5 $lv csi
  wrun $1 $2.$5 $3 $4 $5 $lv tbi
}

G=$D/gen; GI=$D/gi
python3 test/gen_out.py $G 0 0 0
python3 test/gen_index.py $GI
small() { # bin mode
  for v in test/edge/*.vcf; do one $1 edge_$(basename $v .vcf) test/edge/ref.fa $v $2; done
  for v in $G/*.vcf; do one $1 gen_$(basename $v .vcf) test/edge/ref.fa $v $2; done
  for v in $GI/*.vcf; do one $1 gi_$(basename $v .vcf) test/edge/ref.fa $v $2; done
  for v in data/tmp/par/*.vcf; do one $1 par_$(basename $v .vcf) data/tmp/par/par.fa $v $2; done
}
if [ -n "$QUICK" ]; then echo "QUICK: identity runs skipped"; else
  for m in e w; do
    small $N $m
    for v in data/tmp/edge2/*.vcf; do one $N e2_$(basename $v .vcf) data/chr22.fa $v $m; done
    for v in data/tmp/rw/in/*.vcf; do
      n=$(basename $v .vcf); fa=data/tmp/rw/rw.fa; [ $n = scr2 ] && fa=data/chr22.fa
      one $N rw_$n $fa $v $m
    done
    for lv in z z0 z1 z9; do
      wrun $N chr22.$m data/chr22.fa data/hg002.chr22.vcf $m $lv csi; wrun $N chr22.$m data/chr22.fa data/hg002.chr22.vcf $m $lv tbi
      wrun $N scr.$m data/chr22.fa data/scr.vcf $m $lv csi; wrun $N scr.$m data/chr22.fa data/scr.vcf $m $lv tbi
    done
  done
  # With -m -any (records split, law split_*): -m and -W together, by the
  # same rule (the mode word of wrun carries the -m option).
  for lv in z z1; do
    wrun $N chr22m data/chr22.fa data/hg002.chr22.vcf "w -m -any" $lv csi; wrun $N chr22m data/chr22.fa data/hg002.chr22.vcf "w -m -any" $lv tbi
    wrun $N scrm data/chr22.fa data/scr.vcf "w -m -any" $lv csi; wrun $N scrm data/chr22.fa data/scr.vcf "w -m -any" $lv tbi
  done
  for v in test/edge/*.vcf; do
    n=$(basename $v .vcf)
    wrun $N mw_$n test/edge/ref.fa $v "w -m -any" z csi; wrun $N me_$n test/edge/ref.fa $v "e -m -both" z1 tbi
  done
  for B in $PIECES; do small $(realpath $B) w; done
  if [ -n "$BIG" ]; then
    for spec in "kgsub data/hg38.fa data/kg/sub.vcf" "kg22 data/hg38.fa data/kg/chr22.vcf.gz" "all data/hg38.fa data/hg002.all.vcf"; do
      set -- $spec
      wrun $N $1.w $2 $3 w z csi; wrun $N $1.w $2 $3 w z tbi
    done
  fi
  refused=$(ls $D/new/*.refused 2>/dev/null | sed 's|.*/||; s|\.refused$||' | sort | tr '\n' ' ')
  echo "refused by the tool, and so cannot index: ${refused:-none}"
  [ $bad = 0 ] && echo "ALL -W RUNS AS THE RULE SAYS ($cnt runs)"
fi

# 2. Queries on chr22's index.
b2=0
x=$D/new/q.vcf.gz
rm -f $x $x.*
$N norm -W -c w -f data/chr22.fa -o $x data/hg002.chr22.vcf 2> /dev/null
$N norm -c w -f data/chr22.fa data/hg002.chr22.vcf 2> /dev/null | grep -v '^#' > $D/new/q.txt
cp $x $D/new/qc.vcf.gz; bcftools index $D/new/qc.vcf.gz
regs=$(python3 - $x <<'PY'
import struct, sys, zlib
# The first record's POS of blocks 5, 20 and 60: regions that start at a
# block's first record, and end just before it.
d = open(sys.argv[1], "rb").read(); at = 0; poss = []; i = 0
while at < len(d) and len(poss) < 3:
    bs = struct.unpack("<H", d[at + 16:at + 18])[0] + 1
    t = zlib.decompress(d[at + 18:at + bs - 8], -15)
    if i in (5, 20, 60) and t:
        line = t.split(b"\n", 1)[0] if t[:1] != b"#" else b""
        if line: poss.append(int(line.split(b"\t")[1]))
    at += bs; i += 1
print(" ".join("chr22:%d-%d chr22:%d-%d" % (p, p + 20000, p - 5000, p - 1) for p in poss))
PY
)
for R in $regs chr22:16384000-16400000 chr22:16383000-16384000 chr22:20000000-30000000; do
  a=$(tabix $x $R | md5sum); b=$(bcftools view -H -r $R $D/new/qc.vcf.gz | md5sum)
  [ "$a" = "$b" ] || { fail "query $R: tabix and bcftools view differ"; b2=1; }
  lo=${R#*:}; hi=${lo#*-}; lo=${lo%-*}
  if awk -F'\t' -v a=$((lo - 1000)) -v b=$hi '$2 >= a && $2 <= b && length($4) != 1 { f = 1 } END { exit !f }' $D/new/q.txt; then :; else
    c=$(awk -F'\t' -v a=$lo -v b=$hi '$2 >= a && $2 <= b' $D/new/q.txt | md5sum)
    [ "$a" = "$c" ] || { fail "query $R: not the records by POS"; b2=1; }
  fi
done
[ $b2 = 0 ] && echo "QUERIES OK ($(echo $regs | wc -w) + 3 regions)"

# 3. Files.
F=$D/f; S=data/small.vcf; FA=data/hg38.fa
FAA=$R0/$FA; SA=$R0/$S; C22=$R0/data/hg002.chr22.vcf; C22FA=$R0/data/chr22.fa
cc -O1 -shared -fPIC -o $D/fi_shim.so test/fi_shim.c -ldl || fail "cannot build test/fi_shim.c"
SHIM=$(realpath $D/fi_shim.so)
same() { printf '%s\n' "$2" | cmp -s - "$1"; }
state() { # the -o file, the index written, the other name, what else is there
  local f=$1 o out idx oth
  [ $f = csi ] && o=tbi || o=csi
  if same o.vcf.gz 'old output'; then out=old; elif [ ! -s o.vcf.gz ]; then out=empty; elif [ "$(eofhex o.vcf.gz)" = $EOF28 ]; then out=complete; else out=noeof; fi
  if [ ! -e o.vcf.gz.$f ]; then idx=none; elif same o.vcf.gz.$f "old $f"; then idx=old
  else cp o.vcf.gz c.vcf.gz; if [ $f = csi ]; then bcftools index c.vcf.gz 2> /dev/null; else tabix -p vcf c.vcf.gz 2> /dev/null; fi
    cmp -s o.vcf.gz.$f c.vcf.gz.$f && idx=new || idx=WRONG; rm -f c.vcf.gz c.vcf.gz.*; fi
  if [ ! -e o.vcf.gz.$o ]; then oth=none; elif same o.vcf.gz.$o "old $o"; then oth=old; else oth=OTHER; fi
  local extra=$(ls -A | grep -v -x -e err -e o.vcf.gz -e o.vcf.gz.csi -e o.vcf.gz.tbi | tr '\n' ',')
  echo "$out $idx $oth ${extra:-none}"
}
oldf() { rm -f o.* c.*; printf 'old output\n' > o.vcf.gz; printf 'old csi\n' > o.vcf.gz.csi; printf 'old tbi\n' > o.vcf.gz.tbi; }
# fmt label op path nth errno op2 path2 xenv | exit message state
fi1() {
  local f=$1 lbl=$2 op=$3 p=$4 nth=$5 en=$6 op2=$7 p2=$8 xe=$9; shift 9
  local want="$*" w=-W
  [ $f = tbi ] && w=-Wtbi
  oldf
  env $xe LD_PRELOAD=$SHIM FI_OP=$op FI_PATH=$p FI_NTH=$nth FI_ERRNO=$en FI_OP2=$op2 FI_PATH2=$p2 $N norm $w -f $FAA -o o.vcf.gz $SA > /dev/null 2> err; local e=$?
  local got="$e $(grep -v '^framebender:' err | tr '\n' ' ')| $(state $f)"
  [ "$got" = "$want" ] || fail "injection $f $lbl: got [$got], want [$want]"
  cnt=$((cnt + 1))
}
mkdir -p $F/fi; pushd $F/fi > /dev/null
n0=$cnt
for f in csi tbi; do
  [ $f = csi ] && { n1=csi; n2=tbi; } || { n1=tbi; n2=csi; }
  W="error: cannot write o.vcf.gz"
  fi1 $f none none x 1 13 none x "" "0 | complete new none none"
  fi1 $f "1 open -o" open o.vcf.gz 1 13 none x "" "2 $W | old old old none"
  fi1 $f "2 fstat -o" fstat o.vcf.gz 1 13 none x "" "2 $W | old old old none"
  fi1 $f "3 lstat .csi" lstat o.vcf.gz.csi 1 13 none x "" "2 $W.csi | old old old none"
  fi1 $f "3 lstat .tbi" lstat o.vcf.gz.tbi 1 13 none x "" "2 $W.tbi | old old old none"
  fi1 $f "4 the temporary file" open .$f.tmp 1 13 none x "" "2 $W.$f | old old old none"
  fi1 $f "5 rename .csi aside" renameat2 o.vcf.gz.csi 1 13 none x "" "2 $W.csi | old old old none"
  fi1 $f "5 rename .tbi aside" renameat2 o.vcf.gz.tbi 1 13 none x "" "2 $W.tbi | old old old none"
  fi1 $f "5 .tbi aside, EPERM" renameat2 o.vcf.gz.tbi 1 1 none x "" "2 $W.tbi | old old old none"
  fi1 $f "5 .$n2 aside, .$n1 back fails" renameat2 o.vcf.gz.$n2 1 13 renameat2 o.vcf.gz.$n1.old "" "2 $W.$n2 | old none old o.vcf.gz.$n1.old,"
  for en in 22 38 95; do
    fi1 $f "5 no NOREPLACE ($en)" renameat2 "" 1 $en none x "FI_ALL=1" "0 | complete new none none"
  done
  fi1 $f "5 no NOREPLACE, no link" renameat2 "" 1 22 link o.vcf.gz.csi "FI_ALL=1" "2 $W.csi | old old old none"
  fi1 $f "5 no NOREPLACE, link .tbi fails" renameat2 "" 1 22 link o.vcf.gz.tbi "FI_ALL=1" "2 $W.tbi | old old old none"
  fi1 $f "5 no NOREPLACE, unlink .csi fails" renameat2 "" 1 22 unlink o.vcf.gz.csi "FI_ALL=1" "2 $W.csi | old old old none"
  fi1 $f "6 no NOREPLACE, ftruncate" renameat2 "" 1 22 ftruncate o.vcf.gz "FI_ALL=1" "2 $W | old old old none"
  fi1 $f "6 ftruncate -o" ftruncate o.vcf.gz 1 13 none x "" "2 $W | old old old none"
  if [ $f = csi ]; then st6="old none old o.vcf.gz.csi.old,"; else st6="old old none o.vcf.gz.csi.old,"; fi
  fi1 $f "6 ftruncate, .csi back fails" ftruncate o.vcf.gz 1 13 renameat2 o.vcf.gz.csi.old "" "2 $W | $st6"
  fi1 $f "7 unlink .csi.old" unlink o.vcf.gz.csi.old 1 13 none x "" "0 | complete new none o.vcf.gz.csi.old,"
  fi1 $f "7 unlink .tbi.old" unlink o.vcf.gz.tbi.old 1 13 none x "" "0 | complete new none o.vcf.gz.tbi.old,"
  fi1 $f "end: close -o" close o.vcf.gz 1 13 none x "" "2 $W | noeof none none none"
  fi1 $f "end: save" open .$f.tmp 2 13 none x "" "2 $W.$f | noeof none none none"
  fi1 $f "end: rename into place" rename .$f.tmp 1 13 none x "" "2 $W.$f | noeof none none none"
  fi1 $f "end: close of the duplicate" close o.vcf.gz 2 13 none x "" "2 $W | complete none none none"
done
popd > /dev/null
[ $bad = 0 ] && echo "INJECTION OK ($((cnt - n0)) runs)"

b3=0
f3() { fail "$*"; b3=1; }
mkdir -p $F/sch/http:; pushd $F/sch > /dev/null
for o in file:x.vcf.gz data:x.vcf.gz mem:x.vcf.gz chr1:1-1000.vcf.gz http:/x.vcf.gz; do
  for w in -W -Wtbi; do
    f=$(fmt_of $w)
    $N norm $w -f $FAA -o $o $SA 2> /dev/null || f3 "-o $o $w: exit $?"
    files=$(find . -type f | sort | tr '\n' ' ')
    [ "$files" = "./$o ./$o.$f " ] || f3 "-o $o $w: files $files"
    cp ./$o c.vcf.gz; if [ $f = csi ]; then bcftools index c.vcf.gz; else tabix -p vcf c.vcf.gz; fi
    cmp -s ./$o.$f c.vcf.gz.$f || f3 "-o $o $w: not the tool's index"
    rm -f c.vcf.gz c.vcf.gz.* ./$o ./$o.$f
  done
done
popd > /dev/null
pushd $F > /dev/null
rm -f ff.vcf.gz; mkfifo ff.vcf.gz
s=$(date +%s); timeout 20 $N norm -W -f $FAA -o ff.vcf.gz $SA 2> err; e=$?
[ $e = 2 ] && [ "$(grep -v ^framebender err)" = "error: cannot index ff.vcf.gz (not a regular file)" ] && [ $(( $(date +%s) - s )) -lt 10 ] || f3 "FIFO with no reader: exit $e, $(cat err)"
cat ff.vcf.gz > got & rp=$!
timeout 20 $N norm -W -f $FAA -o ff.vcf.gz $SA 2> err; e=$?; sleep 0.5; kill $rp 2> /dev/null; wait $rp 2> /dev/null
[ $e = 2 ] && [ ! -s got ] && grep -q "not a regular file" err || f3 "FIFO with a reader: exit $e, $(stat -c %s got) bytes"
ls ff.vcf.gz.* > /dev/null 2>&1 && f3 "FIFO: an index name made"
rm -f ff.vcf.gz got
$N norm -W -Oz -f $FAA -o /dev/null $SA 2> err; e=$?
[ $e = 2 ] && grep -q "cannot index /dev/null (not a regular file)" err && [ ! -e /dev/null.csi ] || f3 "/dev/null: exit $e"
$N norm -W -Oz -f $FAA -o /dev/stdout $SA 2> err | cat > /dev/null; e=${PIPESTATUS[0]}
[ $e = 2 ] && grep -q "not a regular file" err || f3 "/dev/stdout to a pipe: exit $e"
# names: the -o file (symlink), a directory, an input (symlink, hard link)
rm -f o.* in.vcf; cp $SA in.vcf
printf 'old csi\n' > o.vcf.gz.csi; ln -s o.vcf.gz.csi o.vcf.gz
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write o.vcf.gz.csi (it is the -o file)" err && same o.vcf.gz.csi 'old csi' && [ -L o.vcf.gz ] || f3 "-o a symlink to its .csi: exit $e, $(cat err)"
rm -f o.*; oldf; rm o.vcf.gz.tbi; mkdir o.vcf.gz.tbi
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write o.vcf.gz.tbi" err && same o.vcf.gz 'old output' && same o.vcf.gz.csi 'old csi' || f3 ".tbi a directory: exit $e, $(cat err)"
rmdir o.vcf.gz.tbi; oldf; rm o.vcf.gz.tbi; ln -s in.vcf o.vcf.gz.tbi; m=$(md5sum < in.vcf)
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: output is an input o.vcf.gz.tbi" err && [ "$(md5sum < in.vcf)" = "$m" ] && same o.vcf.gz 'old output' || f3 ".tbi a symlink to the VCF: exit $e, $(cat err)"
oldf; rm o.vcf.gz.csi; ln in.vcf o.vcf.gz.csi
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: output is an input o.vcf.gz.csi" err && [ "$(md5sum < in.vcf)" = "$m" ] || f3 ".csi a hard link to the VCF: exit $e, $(cat err)"
oldf; rm o.vcf.gz.csi; ln -s $FAA.fai o.vcf.gz.csi
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: output is an input o.vcf.gz.csi" err || f3 ".csi a symlink to the .fai: exit $e, $(cat err)"
oldf; rm o.vcf.gz.tbi; ln o.vcf.gz o.vcf.gz.tbi
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write o.vcf.gz.tbi (it is the -o file)" err && same o.vcf.gz 'old output' && same o.vcf.gz.csi 'old csi' || f3 ".tbi a hard link to the -o file: exit $e, $(cat err)"
oldf; $N norm -Wtbi -f $FAA -o o.vcf.gz in.vcf 2>> o.vcf.gz.tbi; e=$?
[ $e = 2 ] && [ "$(head -1 o.vcf.gz.tbi)" = "old tbi" ] && [ "$(tail -1 o.vcf.gz.tbi)" = "error: output is an input o.vcf.gz.tbi" ] && same o.vcf.gz 'old output' && same o.vcf.gz.csi 'old csi' || f3 "stderr's file at .tbi: exit $e, $(tail -1 o.vcf.gz.tbi)"
# an index name that is a symlink to a directory (also the one the -o path
# goes through)
rm -rf o.* dd; mkdir dd; printf 'old output\n' > dd/data; ln -s dd o.vcf.gz.csi; ln -s o.vcf.gz.csi/data o.vcf.gz
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write o.vcf.gz.csi" err && same dd/data 'old output' && [ -L o.vcf.gz.csi ] && [ "$(ls -A dd)" = data ] || f3 "-o through .csi, a symlink to a directory: exit $e, $(cat err)"
rm -f o.*; oldf; rm o.vcf.gz.tbi; ln -s dd o.vcf.gz.tbi
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write o.vcf.gz.tbi" err && same o.vcf.gz 'old output' && same o.vcf.gz.csi 'old csi' && [ -L o.vcf.gz.tbi ] || f3 ".tbi a symlink to a directory: exit $e, $(cat err)"
rm -rf o.* dd
# An older <stem>.csi: htslib reads o.vcf.csi before o.vcf.gz.tbi (shown
# first: a stray one breaks tabix), so -Wtbi is refused, nothing changed, and
# the file left; a CSI is read first, so -W runs; a dangling symlink there is
# not read (stat), so it is not refused. Also a stem cut in a directory name
# (d.x/out: d.csi), and -o x.csi, whose <stem>.csi is the -o file.
mkdir -p st; pushd st > /dev/null
rm -f o.*; $N norm -Wtbi -f $FAA -o o.vcf.gz ../in.vcf 2> /dev/null; tabix -l o.vcf.gz > /dev/null 2>&1 || f3 "tabix -l fails without o.vcf.csi"
printf 'other csi\n' > o.vcf.csi; tabix -l o.vcf.gz > /dev/null 2>&1 && f3 "tabix -l does not read o.vcf.csi"
oldf; printf 'other csi\n' > o.vcf.csi
$N norm -Wtbi -f $FAA -o o.vcf.gz ../in.vcf 2> err; e=$?
[ $e = 2 ] && [ "$(cat err)" = "error: cannot write o.vcf.gz.tbi (htslib would read o.vcf.csi first)" ] && [ "$(state tbi)" = "old old old o.vcf.csi," ] && same o.vcf.csi 'other csi' || f3 "an older o.vcf.csi, -Wtbi: exit $e, $(cat err), $(state tbi)"
oldf; printf 'other csi\n' > o.vcf.csi
$N norm -W -f $FAA -o o.vcf.gz ../in.vcf 2> /dev/null; e=$?
[ $e = 0 ] && [ "$(state csi)" = "complete new none o.vcf.csi," ] && same o.vcf.csi 'other csi' || f3 "an older o.vcf.csi, -W: exit $e, $(state csi)"
oldf; ln -s nowhere o.vcf.csi
$N norm -Wtbi -f $FAA -o o.vcf.gz ../in.vcf 2> /dev/null; e=$?
[ $e = 0 ] && [ "$(state tbi)" = "complete new none o.vcf.csi," ] || f3 "a dangling o.vcf.csi, -Wtbi: exit $e, $(state tbi)"
rm -rf o.* d.x d.csi; mkdir d.x; printf 'other csi\n' > d.csi
$N norm -Oz -Wtbi -f $FAA -o d.x/out ../in.vcf 2> err; e=$?
[ $e = 2 ] && [ "$(cat err)" = "error: cannot write d.x/out.tbi (htslib would read d.csi first)" ] && [ ! -s d.x/out ] && [ "$(ls -A d.x)" = out ] || f3 "an older d.csi for d.x/out: exit $e, $(cat err)"
rm -rf d.x d.csi x.csi x.csi.*
$N norm -Oz -Wtbi -f $FAA -o x.csi ../in.vcf 2> err; e=$?
[ $e = 2 ] && [ "$(cat err)" = "error: cannot write x.csi.tbi (htslib would read x.csi first)" ] && [ ! -e x.csi.tbi ] || f3 "-o x.csi with -Wtbi: exit $e, $(cat err)"
rm -f x.csi x.csi.*
# An existing <name>.old: the moved index goes to <name>.old1 (left there
# when its removal fails), the .old untouched.
oldf; printf 'keep\n' > o.vcf.gz.csi.old
$N norm -W -f $FAA -o o.vcf.gz ../in.vcf 2> /dev/null; e=$?
[ $e = 0 ] && [ "$(state csi)" = "complete new none o.vcf.gz.csi.old," ] && same o.vcf.gz.csi.old keep || f3 "an existing .csi.old: exit $e, $(state csi)"
oldf; printf 'keep\n' > o.vcf.gz.csi.old
LD_PRELOAD=$SHIM FI_OP=unlink FI_PATH=o.vcf.gz.csi.old1 $N norm -W -f $FAA -o o.vcf.gz ../in.vcf 2> /dev/null; e=$?
[ $e = 0 ] && [ "$(state csi)" = "complete new none o.vcf.gz.csi.old,o.vcf.gz.csi.old1," ] && same o.vcf.gz.csi.old keep && same o.vcf.gz.csi.old1 'old csi' || f3 "an existing .csi.old, unlink of .old1 fails: exit $e, $(state csi)"
rm -f o.* err; popd > /dev/null
oldf; chmod 444 o.vcf.gz
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write o.vcf.gz" err && same o.vcf.gz.csi 'old csi' && same o.vcf.gz.tbi 'old tbi' || f3 "a read-only -o: exit $e, $(cat err)"
chmod 644 o.vcf.gz; oldf
$N norm -W -f /nonexistent.fa -o o.vcf.gz in.vcf 2> err; e=$?
[ $e = 2 ] && same o.vcf.gz 'old output' && same o.vcf.gz.csi 'old csi' && same o.vcf.gz.tbi 'old tbi' || f3 "a failure before the open: exit $e"
# BadIdx: before any input is opened (the FASTA is missing), nothing made
for a in "" "-o -" "-o x.vcf" "-Oz -o x.vcf" "-o x" "-Ov -o x.txt"; do
  rm -f x x.*; $N norm -W $a -f /nonexistent.fa in.vcf > out 2> err; e=$?
  [ $e = 2 ] && [ "$(cat err)" = "error: -W needs a BGZF -o file" ] && [ ! -s out ] && ! ls x x.* > /dev/null 2>&1 || f3 "-W [$a]: exit $e, $(cat err)"
done
# A driver error after the open, and Bend's runtime stopping: no index (the
# old ones removed); the runtime's _exit leaves the temporary file.
rm -f o.* z.vcf.gz cut.vcf.gz; bgzip -c $C22 > z.vcf.gz; head -c $(( $(stat -c %s z.vcf.gz) / 2 )) z.vcf.gz > cut.vcf.gz
oldf; $N norm -W -f $FAA -o o.vcf.gz cut.vcf.gz 2> err; e=$?
[ $e = 2 ] && grep -q "error: bad BGZF cut.vcf.gz" err && [ "$(ls o.* | tr '\n' ' ')" = "o.vcf.gz " ] || f3 "a cut BGZF input: exit $e, files $(ls o.*)"
{ cat $C22; printf 'chr22\t300000000000000\t.\tA\t<DEL>\t.\t.\tSVLEN=-1\n'; } > nat.vcf
oldf; $N norm -W -c w -f $C22FA -o o.vcf.gz nat.vcf 2> err; e=$?
[ $e = 1 ] && grep -q "^bend: a Nat past" err && [ "$(ls o.* | tr '\n' ' ')" = "o.vcf.gz o.vcf.gz.csi.tmp " ] || f3 "Bend's runtime stops: exit $e, files $(ls o.*)"
rm -f nat.vcf z.vcf.gz cut.vcf.gz
# A taken temporary name, the mode, the mtime, and a run without -W after it.
rm -f o.*; printf 'stray\n' > o.vcf.gz.csi.tmp
$N norm -W -f $FAA -o o.vcf.gz in.vcf 2> /dev/null; e=$?
[ $e = 0 ] && same o.vcf.gz.csi.tmp stray && [ "$(ls o.* | tr '\n' ' ')" = "o.vcf.gz o.vcf.gz.csi o.vcf.gz.csi.tmp " ] || f3 "a taken temporary name: exit $e, files $(ls o.*)"
for um in 022 077; do
  rm -f o.*; (umask $um; $N norm -W -f $FAA -o o.vcf.gz in.vcf 2> /dev/null)
  want=$([ $um = 022 ] && echo 644 || echo 600)
  [ "$(stat -c %a o.vcf.gz.csi)" = $want ] || f3 "umask $um: mode $(stat -c %a o.vcf.gz.csi)"
  [ ! o.vcf.gz.csi -ot o.vcf.gz ] || f3 "the index is older than the file"
done
$N norm -f $FAA -o o.vcf.gz in.vcf 2> /dev/null
[ -e o.vcf.gz.csi ] || f3 "a run without -W removed the old index (it must leave it)"
rm -f o.* in.vcf err out
popd > /dev/null
[ $b3 = 0 ] && echo "FILES OK"

# 4. Builds.
b4=0
if [ -n "$NOHTS" ]; then
  rm -f $F/nh.vcf.gz; $NOHTS norm -W -f $FA -o $F/nh.vcf.gz $S > /dev/null 2> $F/err; e=$?
  [ $e = 2 ] && [ "$(cat $F/err)" = "error: no index in this build $F/nh.vcf.gz" ] && [ ! -e $F/nh.vcf.gz ] || { fail "NOHTS: exit $e, $(cat $F/err)"; b4=1; }
fi
if [ -n "$PLAIN" ]; then
  $PLAIN norm -W -f $FA -o $F/nh.vcf.gz $S > /dev/null 2> $F/err; e=$?
  [ $e = 2 ] && [ "$(cat $F/err)" = "error: no BGZF in this build $F/nh.vcf.gz" ] || { fail "PLAIN: exit $e, $(cat $F/err)"; b4=1; }
fi
if [ -z "$SKIPBUILD" ]; then
  for pc in $HOME/.local/opt/htslib-1.24/lib/pkgconfig /nonexistent; do
    rm -f $F/never; PKG_CONFIG_PATH=$pc ./build.sh $F/never > /dev/null 2> $F/err; e=$?
    [ $e != 0 ] && grep -q "tools/build_htslib.sh" $F/err && [ ! -e $F/never ] || { fail "build.sh with PKG_CONFIG_PATH=$pc: exit $e"; b4=1; }
  done
  printf 'x' > $F/bad.tar.bz2
  tools/build_htslib.sh $F/never $F/bad.tar.bz2 > /dev/null 2> $F/err; e=$?
  [ $e != 0 ] && grep -q "SHA-256" $F/err && [ ! -e $F/never ] || { fail "build_htslib.sh with a wrong tarball: exit $e"; b4=1; }
  rm -f $F/bad.tar.bz2
fi
[ $b4 = 0 ] && echo "BUILDS OK${NOHTS:+ (no htslib)}${PLAIN:+ (plain)}$([ -z "$SKIPBUILD" ] && echo " (build.sh, build_htslib.sh)")"

# 5. Usage errors.
u=0
for a in -Wbai -W=TBI -W= --write --write-index=bai --write-index==tbi "-W tbi"; do
  $N norm -f $FA $S $a > $F/u.out 2> $F/u.err; c=$?
  if [ $c != 2 ] || [ -s $F/u.out ] || ! grep -q '^usage: framebender norm' $F/u.err; then fail "usage [$a] exit $c"; u=1; fi
done
[ $u = 0 ] && echo "USAGE ERRORS OK"

# 6. The threads seen (Linux): -W keeps the constructor's --threads.
if [ -d /proc/self/task ]; then
  seen() { # args...
    rm -f $F/t.vcf.gz*
    $N "$@" > /dev/null 2>&1 & local pid=$! mx=0
    while kill -0 $pid 2> /dev/null; do
      local n=$(ls /proc/$pid/task 2> /dev/null | wc -l); [ "$n" -gt $mx ] && mx=$n
    done
    wait $pid; echo $mx
  }
  base=$(seen norm --threads 3 -f data/chr22.fa -o $F/t.vcf.gz data/hg002.chr22.vcf)
  line="--threads 3 -o: $base;"
  for w in "${SP[@]}"; do
    t=$(seen norm $w --threads 3 -f data/chr22.fa -o $F/t.vcf.gz data/hg002.chr22.vcf)
    line="$line $w $t;"
    [ $t -le $((base + 2)) ] || fail "threads with $w: $t, without -W $base"
  done
  echo "threads seen: $line"
  rm -f $F/t.vcf.gz*
fi
[ $bad = 0 ] && echo "ALL PASS" || echo "SOME FAIL"
exit $bad
