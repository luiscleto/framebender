#!/usr/bin/env bash
# test/out.sh NEW [DIR]: the output options -o and -O (law output) and the
# driver's BGZF writer, on binary NEW. Results go to DIR (default
# data/tmp/out/t). Needs bgzip, tabix and bcftools (htslib 1.24, with
# libdeflate 1.26 for the byte-identity checks), prlimit and python3.
#
# 1. Identity: on the edge cases, the batch-boundary cases (test/gen_par.py),
#    the generated cases (test/gen_edge.py, test/gen_rw.py), chr22, the
#    scrambled file and test/gen_out.py's block-cut cases, under -c e and
#    -c w, each output form below runs with --threads N (N = 1, 2, 3, 7, 16,
#    32, 128 in turn) and the options at three positions. Stderr and the exit
#    code must be those of the run without output options (the plain run).
#    The output must be: when it is plain, the plain run's stdout; when it is
#    BGZF, byte for byte bgzip -l L of that stdout, and when the run does not
#    end with code 0, the same without the 28-byte end-of-file block. Then
#    chr22 at every level 0 to 9, and bgzip -t, tabix and bcftools view on
#    chr22's output.
# 2. Failures: inputs that fail leave an existing -o file unchanged; a VCF
#    cut mid-file leaves a file without the end-of-file block; full disks and
#    failed writes (/dev/full, a file size limit inside the header, mid-file
#    and at the end-of-file block) stop with "cannot write", exit 2, and no
#    end-of-file block; so does a closed pipe, as for plain output.
# 3. Files: -o naming an input (the VCF, the FASTA, the .fai, through a
#    symlink and a hard link) or stderr's file is refused, the input
#    unchanged; directories and missing directories; new files get 0666 less
#    the umask, an existing file keeps its mode and is emptied; /dev/stdout,
#    a FIFO, /dev/null.
# 4. Usage errors. 5. framebender reads its own BGZF output. 6. Threads seen.
# 7. With NOLIB=binary, a build without libdeflate. Exits 0 when all pass.
# QUICK=1 skips the identity runs of 1.
cd "$(dirname "$0")/.."
N=$(realpath "$1"); D=${2:-data/tmp/out/t}
export BEND_NO_TELEMETRY=1
mkdir -p $D/ref $D/new $D/gen $D/want
EOF28=1f8b08040000000000ff0600424302001b0003000000000000000000
bad=0; cnt=0
NS=(1 2 3 7 16 32 128)
fail() { echo "FAIL $*"; bad=1; }
eofhex() { tail -c 28 "$1" | od -An -tx1 | tr -d ' \n'; }

# The BGZF bytes expected for the plain text of $tag at level $1, exit code $2.
want() { # tag level code
  local w=$D/want/$1.$2.$3
  if [ ! -f $w ]; then
    bgzip -c -l $2 < $D/ref/$1.out > $w
    [ "$3" != 0 ] && truncate -s -28 $w
  fi
  echo $w
}

# Output forms: where (s: stdout, o: the file @), what (z: BGZF at a level, p:
# plain), options.
FORMS=(
  "o z 6 -o @.vcf.gz"
  "s z 6 -Oz"
  "s z 1 -O z1"
  "o z 0 -Oz0 -o @.out"
  "o z 9 -o @.vcf.bgz -Oz9"
  "o p - -o @.vcf -Oz"
  "s p - -o -"
  "o z 9 -Oz9 -Ov -o @.VCF.GZ"
  "s z 0 -Oz0 -Oz"
  "s p - -Ov"
)
k=0
ref() { # tag fasta vcf mode: the plain run
  if [ ! -f $D/ref/$1.code ]; then
    nice -n 19 timeout 900 $N norm -c $4 -f $2 $3 > $D/ref/$1.out 2> $D/ref/$1.err; echo $? > $D/ref/$1.code
  fi
}
one() { # name fasta vcf mode
  local tag=$1.$4 fa=$2 v=$3 m=$4
  ref $tag $fa $v $m
  local code=$(cat $D/ref/$tag.code)
  for f in "${FORMS[@]}"; do
    set -- $f; local where=$1 what=$2 lv=$3; shift 3
    local o=${*//@/$D\/new\/$tag}; local n=${NS[$((k % 7))]} p=$((k % 3)); k=$((k + 1))
    local file=$D/new/$tag.stdout
    [ $where = o ] && { for w in $o; do case $w in $D/new/*) file=$w;; esac; done; rm -f $file; }
    local opts="--threads $n $o"
    case $p in
      0) set -- norm $opts -c $m -f $fa $v ;;
      1) set -- norm -c $m -f $fa $opts $v ;;
      2) set -- norm -c $m -f $fa $v $opts ;;
    esac
    nice -n 19 timeout 900 $N "$@" > $D/new/$tag.stdout 2> $D/new/$tag.err; local c=$?
    cnt=$((cnt + 1))
    [ $c = $code ] || fail "$tag [$*]: exit $c, plain run $code"
    cmp -s $D/new/$tag.err $D/ref/$tag.err || fail "$tag [$*]: stderr differs"
    [ $where = o ] && [ -s $D/new/$tag.stdout ] && fail "$tag [$*]: wrote to stdout"
    if [ $what = p ]; then
      cmp -s $file $D/ref/$tag.out || fail "$tag [$*]: plain output differs"
    else
      cmp -s $file $(want $tag $lv $code) || fail "$tag [$*]: not bgzip -l $lv's bytes"
    fi
  done
}

# Test/gen_out.py's header case: the output's header (all lines before the
# first record) ends exactly at a block boundary, then is longer than a block
# and ends at the next one.
G=$D/gen
python3 test/gen_out.py $G 0 0 0
hdr() { $N norm -c w -f test/edge/ref.fa $G/$1.vcf 2>/dev/null | python3 -c '
import sys
d = sys.stdin.buffer.read(); i = 0
while i < len(d) and d[i:i+1] == b"#": i = d.index(b"\n", i) + 1
print(i)'; }
tot() { $N norm -c w -f test/edge/ref.fa $G/$1.vcf 2>/dev/null | wc -c; }
h1=$(hdr hdrwin); h2=$(hdr hdrwin2); t3=$(tot tailwin)
python3 test/gen_out.py $G $((65280 - h1)) $((130560 - h2)) $((65280 - t3))
[ "$(hdr hdrwin)" = 65280 ] && [ "$(hdr hdrwin2)" = 130560 ] && [ "$(tot tailwin)" = 65280 ] || fail "hdrwin, tailwin: $(hdr hdrwin), $(hdr hdrwin2) and $(tot tailwin) bytes"

[ -n "$QUICK" ] && echo "QUICK: identity runs skipped" || for m in e w; do
  for v in test/edge/*.vcf; do one edge_$(basename $v .vcf) test/edge/ref.fa $v $m; done
  for v in data/tmp/par/*.vcf; do one par_$(basename $v .vcf) data/tmp/par/par.fa $v $m; done
  for v in data/tmp/edge2/*.vcf; do one e2_$(basename $v .vcf) data/chr22.fa $v $m; done
  for v in data/tmp/rw/in/*.vcf; do
    n=$(basename $v .vcf); fa=data/tmp/rw/rw.fa; [ $n = scr2 ] && fa=data/chr22.fa
    one rw_$n $fa $v $m
  done
  one chr22 data/chr22.fa data/hg002.chr22.vcf $m
  one scr data/chr22.fa data/scr.vcf $m
  for v in $G/*.vcf; do one gen_$(basename $v .vcf) test/edge/ref.fa $v $m; done
done
[ -z "$QUICK" ] && [ $bad = 0 ] && echo "ALL IDENTICAL ($cnt runs)"

# chr22 at every level, and the tools on the default output.
ref chr22.e data/chr22.fa data/hg002.chr22.vcf e
b2=0
for l in 0 1 2 3 4 5 6 7 8 9; do
  $N norm -c e -f data/chr22.fa -Oz$l data/hg002.chr22.vcf 2>/dev/null | cmp -s - $(want chr22.e $l 0) || { fail "chr22 -Oz$l"; b2=1; }
done
x=$D/new/c22.vcf.gz
rm -f $x $x.tbi
$N norm -c e -f data/chr22.fa -o $x data/hg002.chr22.vcf 2>/dev/null
bgzip -t $x || { fail "bgzip -t"; b2=1; }
[ "$(eofhex $x)" = $EOF28 ] || { fail "no end-of-file block"; b2=1; }
tabix -p vcf $x || { fail "tabix"; b2=1; }
[ "$(bcftools view -H $x | wc -l)" = "$(grep -vc '^#' $D/ref/chr22.e.out)" ] || { fail "bcftools view count"; b2=1; }
[ "$(tabix $x chr22:20000000-21000000 | md5sum)" = "$(awk -F'\t' '!/^#/ && $2 >= 20000000 && $2 <= 21000000' $D/ref/chr22.e.out | md5sum)" ] || { fail "tabix query"; b2=1; }
[ $b2 = 0 ] && echo "LEVELS 0-9 AND TOOLS OK"

# 2. Failures.
b3=0
old() { printf 'old file\n' > $1; }
ex=$D/new/exists.vcf.gz
gzip -c test/edge/sorted.vcf > $D/new/plain.gz
mkdir -p $D/new/adir
for c in "-f data/chr22.fa $D/new/missing.vcf" "-f data/chr22.fa $D/new/plain.gz" "-f $D/new/missing.fa data/hg002.chr22.vcf" "-f test/edge/ref.fa $D/new/adir"; do
  old $ex
  $N norm -o $ex $c > /dev/null 2> $D/new/f.err; e=$?
  [ $e = 2 ] && [ "$(cat $ex)" = "old file" ] || { fail "input error [$c]: exit $e, -o file $(head -c 20 $ex | od -c | head -1)"; b3=1; }
done
# A VCF cut mid-file (bad BGZF): exit 2, the file without the end-of-file block.
bgzip -c data/hg002.chr22.vcf | head -c 1000000 > $D/new/cut.vcf.gz
$N norm -c e -f data/chr22.fa -o $ex $D/new/cut.vcf.gz > /dev/null 2> $D/new/f.err; e=$?
[ $e = 2 ] && grep -q '^error: bad BGZF' $D/new/f.err && [ "$(eofhex $ex)" != $EOF28 ] || { fail "cut VCF: exit $e"; b3=1; }
prefix() { local n=$(wc -c < $1); cmp -s $1 <(head -c $n $2); }
$N norm -c e -f data/chr22.fa $D/new/cut.vcf.gz > $D/new/cut.plain 2>/dev/null
bgzip -dc $ex > $D/new/cut.txt 2>/dev/null
prefix $D/new/cut.txt $D/new/cut.plain || { fail "cut VCF: not a prefix of the plain run"; b3=1; }
# Failed writes.
for o in "-o /dev/full" "-o /dev/full -Oz"; do
  $N norm -c e -f data/chr22.fa $o data/hg002.chr22.vcf > /dev/null 2> $D/new/f.err; e=$?
  [ $e = 2 ] && grep -qx 'error: cannot write /dev/full' $D/new/f.err || { fail "[$o]: exit $e $(cat $D/new/f.err)"; b3=1; }
done
$N norm -c e -f data/chr22.fa -Oz data/hg002.chr22.vcf > /dev/full 2> $D/new/f.err; e=$?
[ $e = 2 ] && grep -qx 'error: cannot write' $D/new/f.err || { fail "stdout /dev/full: exit $e"; b3=1; }
full=$(wc -c < $(want chr22.e 6 0))
for lim in 1000 300000 $((full - 28)) $((full - 10)); do
  for x in $D/new/lim.vcf.gz $D/new/lim.vcf; do
    rm -f $x
    prlimit --fsize=$lim $N norm -c e -f data/chr22.fa -o $x data/hg002.chr22.vcf 2>&1 > /dev/null | cat > $D/new/f.err; e=${PIPESTATUS[0]}
    [ $e = 2 ] && grep -qx "error: cannot write $x" $D/new/f.err && [ "$(wc -c < $x)" -le $lim ] || { fail "size limit $lim $x: exit $e $(cat $D/new/f.err)"; b3=1; }
    if [ $x = $D/new/lim.vcf.gz ]; then
      [ "$(eofhex $x)" != $EOF28 ] || { fail "size limit $lim: end-of-file block written"; b3=1; }
      prefix $x $(want chr22.e 6 0) || { fail "size limit $lim: not a prefix"; b3=1; }
    else
      prefix $x $D/ref/chr22.e.out || { fail "size limit $lim plain: not a prefix"; b3=1; }
    fi
  done
done
# A close that fails after the end-of-file block (an LD_PRELOAD shim): exit
# 2, the block cut off again (through a duplicate of the descriptor). With
# FB_CLOSEFAIL_REPOINT, the shim also moves the file away and points its path
# at another file before failing: that file must be untouched, and the moved
# file cut. Under umask 0777 (a file that cannot be opened again by its
# path) the block is cut off too. When the take-back fails itself (the
# truncate fails: FB_TRUNCFAIL), or the file's close succeeds and the
# duplicate's fails (FB_CLOSEFAIL_NTH=2), the run still exits 2 with "cannot
# write" and the file keeps its end-of-file block.
cat > $D/new/closefail.c <<'C'
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
static int is_want(int fd, const char* want) {
  char link[64], path[PATH_MAX];
  snprintf(link, sizeof link, "/proc/self/fd/%d", fd);
  ssize_t n = want ? readlink(link, path, sizeof path - 1) : -1;
  return n > 0 && (path[n] = 0, strcmp(path, want) == 0);
}
int ftruncate(int fd, off_t len) {
  static int (*real)(int, off_t);
  if (!real) real = dlsym(RTLD_NEXT, "ftruncate");
  if (len > 0 && getenv("FB_TRUNCFAIL") && is_want(fd, getenv("FB_CLOSEFAIL"))) { errno = EIO; return -1; }
  return real(fd, len);
}
int close(int fd) {
  static int (*real)(int);
  static int seen = 0;
  if (!real) real = dlsym(RTLD_NEXT, "close");
  const char* want = getenv("FB_CLOSEFAIL");
  const char* nth = getenv("FB_CLOSEFAIL_NTH");
  int hit = is_want(fd, want) && (seen += 1, !nth || seen == atoi(nth));
  int r = real(fd);
  if (hit) {
    const char* to = getenv("FB_CLOSEFAIL_REPOINT");
    if (to) {
      char moved[PATH_MAX + 8];
      snprintf(moved, sizeof moved, "%s.moved", want);
      if (rename(want, moved) != 0 || symlink(to, want) != 0) return r;
    }
    errno = EIO;
    return -1;
  }
  return r;
}
C
cc -shared -fPIC -O2 -o $D/new/closefail.so $D/new/closefail.c -ldl
x=$(realpath $D/new)/cf.vcf.gz; rm -f $x
FB_CLOSEFAIL=$x LD_PRELOAD=$D/new/closefail.so $N norm -c e -f data/chr22.fa -o $x data/hg002.chr22.vcf > /dev/null 2> $D/new/f.err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write $x" $D/new/f.err && cmp -s $x $(want chr22.e 6 1) || { fail "close failure: exit $e $(tail -1 $D/new/f.err)"; b3=1; }
cp test/edge/ref.fa $D/new/victim.fa; v0=$(md5sum < $D/new/victim.fa)
rm -f $x $x.moved
FB_CLOSEFAIL=$x FB_CLOSEFAIL_REPOINT=$(realpath $D/new/victim.fa) LD_PRELOAD=$D/new/closefail.so $N norm -c e -f data/chr22.fa -o $x data/hg002.chr22.vcf > /dev/null 2> $D/new/f.err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write $x" $D/new/f.err && [ "$(md5sum < $D/new/victim.fa)" = "$v0" ] && cmp -s $x.moved $(want chr22.e 6 1) || { fail "close failure, path re-pointed: exit $e, the other file $( [ "$(md5sum < $D/new/victim.fa)" = "$v0" ] && echo kept || echo CUT)"; b3=1; }
rm -f $x $x.moved
( umask 0777; FB_CLOSEFAIL=$x LD_PRELOAD=$D/new/closefail.so exec $N norm -c e -f data/chr22.fa -o $x data/hg002.chr22.vcf ) > /dev/null 2> $D/new/f.err; e=$?
chmod 600 $x
[ $e = 2 ] && grep -qx "error: cannot write $x" $D/new/f.err && cmp -s $x $(want chr22.e 6 1) || { fail "close failure under umask 0777: exit $e"; b3=1; }
for y in $x $(realpath $D/new)/cf.vcf; do
  rm -f $y; w=$(want chr22.e 6 0); [ $y = $x ] || w=$D/ref/chr22.e.out
  FB_CLOSEFAIL=$y FB_CLOSEFAIL_NTH=2 LD_PRELOAD=$D/new/closefail.so $N norm -c e -f data/chr22.fa -o $y data/hg002.chr22.vcf > /dev/null 2> $D/new/f.err; e=$?
  [ $e = 2 ] && grep -qx "error: cannot write $y" $D/new/f.err && cmp -s $y $w || { fail "the duplicate's close fails [$y]: exit $e"; b3=1; }
done
rm -f $x
FB_CLOSEFAIL=$x FB_TRUNCFAIL=1 LD_PRELOAD=$D/new/closefail.so $N norm -c e -f data/chr22.fa -o $x data/hg002.chr22.vcf > /dev/null 2> $D/new/f.err; e=$?
[ $e = 2 ] && grep -qx "error: cannot write $x" $D/new/f.err && cmp -s $x $(want chr22.e 6 0) || { fail "the take-back's truncate fails: exit $e"; b3=1; }
# One write of the output fails with EIO (an LD_PRELOAD shim: the k-th write
# to the file, once; later ones would succeed): exit 2, "cannot write", and
# the file a prefix of bgzip's bytes (or of the plain text) without the
# end-of-file block: a writer that went on would leave a gap.
cat > $D/new/writefail.c <<'C'
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
ssize_t write(int fd, const void* p, size_t n) {
  static ssize_t (*real)(int, const void*, size_t);
  static int seen = 0;
  if (!real) real = dlsym(RTLD_NEXT, "write");
  const char* want = getenv("FB_WRITEFAIL");
  char link[64], path[PATH_MAX];
  snprintf(link, sizeof link, "/proc/self/fd/%d", fd);
  ssize_t k = want && fd > 2 ? readlink(link, path, sizeof path - 1) : -1;
  if (k > 0 && (path[k] = 0, strcmp(path, want) == 0) && __atomic_add_fetch(&seen, 1, __ATOMIC_SEQ_CST) == atoi(getenv("FB_WRITEFAIL_K"))) {
    errno = EIO;
    return -1;
  }
  return real(fd, p, n);
}
C
cc -shared -fPIC -O2 -o $D/new/writefail.so $D/new/writefail.c -ldl
for x in $(realpath $D/new)/wf.vcf.gz $(realpath $D/new)/wf.vcf; do
  rm -f $x
  FB_WRITEFAIL=$x FB_WRITEFAIL_K=3 LD_PRELOAD=$D/new/writefail.so $N norm -c e -f data/chr22.fa -o $x data/hg002.chr22.vcf > /dev/null 2> $D/new/f.err; e=$?
  w=$D/ref/chr22.e.out; case $x in *.gz) w=$(want chr22.e 6 0);; esac
  [ $e = 2 ] && grep -qx "error: cannot write $x" $D/new/f.err && [ -s $x ] && [ "$(eofhex $x)" != $EOF28 ] && prefix $x $w || { fail "one failed write [$x]: exit $e, $(wc -c < $x) bytes"; b3=1; }
done
# A transient failure: stdout a non-blocking pipe whose reader waits (the
# pipe fills: EAGAIN once). Exit 2, "cannot write", and what arrives is a
# prefix of bgzip's bytes, without the end-of-file block: nothing after the
# failed write.
python3 - $N $D/new/eagain.gz <<'PY' > $D/new/eagain.txt
import fcntl, os, subprocess, sys, time
r, w = os.pipe()
fcntl.fcntl(w, fcntl.F_SETFL, fcntl.fcntl(w, fcntl.F_GETFL) | os.O_NONBLOCK)
p = subprocess.Popen([sys.argv[1], 'norm', '-c', 'e', '-f', 'data/chr22.fa', '-Oz', 'data/hg002.chr22.vcf'], stdout=w, stderr=subprocess.PIPE)
os.close(w)
time.sleep(2)
with open(sys.argv[2], 'wb') as f:
    while True:
        b = os.read(r, 1 << 20)
        if not b:
            break
        f.write(b)
err = p.stderr.read().decode()
print(p.wait(), err.strip().split('\n')[-1])
PY
[ "$(cat $D/new/eagain.txt)" = "2 error: cannot write" ] && [ "$(eofhex $D/new/eagain.gz)" != $EOF28 ] && prefix $D/new/eagain.gz $(want chr22.e 6 0) || { fail "EAGAIN: $(cat $D/new/eagain.txt)"; b3=1; }
# A closed pipe: as for plain output (Bend's runtime ignores SIGPIPE), the
# write fails: "cannot write", exit 2.
set -o pipefail
$N norm -c e -f data/chr22.fa -Oz data/hg002.chr22.vcf 2> $D/new/f.err | head -c 100 > /dev/null; e=$?
set +o pipefail
[ $e = 2 ] && grep -qx 'error: cannot write' $D/new/f.err || { fail "closed pipe: exit $e"; b3=1; }
[ $b3 = 0 ] && echo "FAILURES OK"

# 3. Files.
b4=0
W=$D/new/files; rm -rf $W; mkdir -p $W
cp data/hg002.chr22.vcf $W/in.vcf; cp test/edge/ref.fa $W/r.fa; cp test/edge/ref.fa.fai $W/r.fa.fai; cp test/edge/sorted.vcf $W/s.vcf
ln -s in.vcf $W/link.vcf; ln $W/s.vcf $W/hard.vcf
sums() { md5sum $W/in.vcf $W/r.fa $W/r.fa.fai $W/s.vcf | md5sum; }
s0=$(sums)
for c in "-f data/chr22.fa -o $W/in.vcf $W/in.vcf" "-f data/chr22.fa -o $W/link.vcf $W/in.vcf" "-f $W/r.fa -o $W/r.fa $W/s.vcf" "-f $W/r.fa -o $W/r.fa.fai $W/s.vcf" "-f $W/r.fa -o $W/hard.vcf $W/s.vcf" "-f $W/r.fa -Oz -o $W/s.vcf $W/hard.vcf"; do
  $N norm $c > /dev/null 2> $D/new/f.err; e=$?
  [ $e = 2 ] && grep -q '^error: output is an input ' $D/new/f.err || { fail "[$c]: exit $e $(cat $D/new/f.err)"; b4=1; }
done
[ "$(sums)" = "$s0" ] || { fail "an input changed"; b4=1; }
# Pipes and FIFOs as inputs: the VCF on a pipe named by -o (/dev/stdin,
# /proc/self/fd/0), one FIFO as the VCF and -o: refused, no hang.
for o in /dev/stdin /proc/self/fd/0; do
  cat $W/s.vcf | timeout 60 $N norm -c w -f $W/r.fa -o $o /dev/stdin > /dev/null 2> $D/new/f.err; e=$?
  [ $e = 2 ] && grep -qx "error: output is an input $o" $D/new/f.err || { fail "pipe [-o $o]: exit $e"; b4=1; }
done
mkfifo $W/vf; (timeout 60 cat $W/s.vcf > $W/vf 2>/dev/null &)
timeout 60 $N norm -c w -f $W/r.fa -o $W/vf $W/vf > /dev/null 2> $D/new/f.err; e=$?
[ $e = 2 ] && grep -qx "error: output is an input $W/vf" $D/new/f.err || { fail "FIFO input [-o $W/vf]: exit $e"; b4=1; }
timeout 5 cat $W/vf > /dev/null 2>&1
# Output and messages on one pipe or FIFO are what the user asked for:
# -o /dev/stderr with stderr a FIFO, -o /dev/stdout 2>&1 into a pipe.
mkfifo $W/ef; (timeout 60 cat $W/ef > $W/ef.out &)
timeout 60 $N norm -c w -f $W/r.fa -o /dev/stderr $W/s.vcf > /dev/null 2> $W/ef; e=$?; sleep 1
[ $e = 0 ] && grep -q '^##fileformat' $W/ef.out && grep -q '^framebender: ' $W/ef.out || { fail "-o /dev/stderr, stderr a FIFO: exit $e"; b4=1; }
timeout 60 $N norm -c w -f $W/r.fa -o /dev/stdout $W/s.vcf 2>&1 | cat > $W/so.out; e=${PIPESTATUS[0]}
[ $e = 0 ] && grep -q '^##fileformat' $W/so.out && grep -q '^framebender: ' $W/so.out || { fail "-o /dev/stdout 2>&1 | cat: exit $e"; b4=1; }
$N norm -f $W/r.fa -o $W/err.vcf.gz $W/s.vcf > /dev/null 2> $W/err.vcf.gz; e=$?
[ $e = 2 ] && grep -q 'output is an input' $W/err.vcf.gz || { fail "-o stderr's file: exit $e"; b4=1; }
for o in $W/adir/ $W/no/such.vcf $W/ro/x.vcf; do
  mkdir -p $W/adir $W/ro; chmod 555 $W/ro
  $N norm -f $W/r.fa -o $o $W/s.vcf > /dev/null 2> $D/new/f.err; e=$?
  [ $e = 2 ] && grep -qx "error: cannot write $o" $D/new/f.err && [ ! -e $W/ro/x.vcf ] || { fail "[-o $o]: exit $e $(cat $D/new/f.err)"; b4=1; }
  chmod 755 $W/ro
done
( umask 022; $N norm -f $W/r.fa -o $W/m1.vcf $W/s.vcf 2>/dev/null )
( umask 077; $N norm -f $W/r.fa -Oz -o $W/m2.vcf.gz $W/s.vcf 2>/dev/null )
[ "$(stat -c %a $W/m1.vcf)" = 644 ] && [ "$(stat -c %a $W/m2.vcf.gz)" = 600 ] || { fail "modes $(stat -c %a $W/m1.vcf) $(stat -c %a $W/m2.vcf.gz)"; b4=1; }
head -c 5000000 /dev/zero > $W/big.vcf; chmod 640 $W/big.vcf
( umask 022; $N norm -f $W/r.fa -o $W/big.vcf $W/s.vcf 2>/dev/null )
[ "$(stat -c %a $W/big.vcf)" = 640 ] && cmp -s $W/big.vcf <($N norm -f $W/r.fa $W/s.vcf 2>/dev/null) || { fail "existing file not emptied or its mode changed"; b4=1; }
$N norm -f $W/r.fa -o /dev/stdout $W/s.vcf 2>/dev/null | cmp -s - <($N norm -f $W/r.fa $W/s.vcf 2>/dev/null) || { fail "-o /dev/stdout"; b4=1; }
$N norm -c w -f $W/r.fa -o /dev/null -Oz $W/s.vcf 2>/dev/null || { fail "-o /dev/null"; b4=1; }
mkfifo $W/fifo; cat $W/fifo > $W/fifo.out & $N norm -c e -f data/chr22.fa -Oz -o $W/fifo data/hg002.chr22.vcf 2>/dev/null; wait
cmp -s $W/fifo.out $(want chr22.e 6 0) || { fail "FIFO"; b4=1; }
[ $b4 = 0 ] && echo "FILES OK"

# 4. Usage errors.
u=0
for a in "-Ob" "-Ou" "-O b" "-Oz10" "-Ov5" "-O5" "-Ox" "-OZ" "-O" "-o" "-o x.bcf" "-o X.BCF" "-Ox -Oz" "-ox.vcf.gz"; do
  $N norm -c e -f data/chr22.fa data/hg002.chr22.vcf $a > $D/u.out 2> $D/u.err; c=$?
  if [ $c != 2 ] || [ -s $D/u.out ] || ! grep -q '^usage: framebender norm' $D/u.err; then fail "usage [$a] exit $c"; u=1; fi
done
[ $u = 0 ] && echo "USAGE ERRORS OK"

# 5. The round trip: framebender on its own BGZF output gives the same as on
# its plain output.
$N norm -c e -f data/chr22.fa data/hg002.chr22.vcf 2>/dev/null > $D/new/rt.vcf
$N norm -c e -f data/chr22.fa -o $D/new/rt.vcf.gz data/hg002.chr22.vcf 2>/dev/null
cmp -s <($N norm -c e -f data/chr22.fa $D/new/rt.vcf 2>&1) <($N norm -c e -f data/chr22.fa $D/new/rt.vcf.gz 2>&1 | sed "s|rt.vcf.gz|rt.vcf|g") && echo "ROUND TRIP OK" || fail "round trip"

# 6. The threads a run starts (Linux): Bend's workers follow --threads with
# -o and -O on the line too; BGZF adds N compressors and one writer.
if [ -d /proc/self/task ]; then
  for a in "--threads 3" "--threads 3 -Oz -o $D/new/th.vcf.gz" "-o $D/new/th.vcf --threads 3"; do
    $N norm $a -f data/chr22.fa data/hg002.chr22.vcf > /dev/null 2>&1 & pid=$!
    mx=0
    while kill -0 $pid 2>/dev/null; do
      t=$(ls /proc/$pid/task 2>/dev/null | wc -l); [ "$t" -gt $mx ] && mx=$t
    done
    wait $pid
    echo "[$a]: at most $mx threads seen"
    # Bend's 3 workers and the driver's helpers (and 4 more with -Oz); a
    # constructor that refused the line would leave one worker per CPU.
    lim=12; case $a in *-Oz*) lim=16;; esac
    [ $mx -le $lim ] || fail "[$a]: $mx threads, more than $lim"
  done
fi

# 7. A build without libdeflate (NOLIB=binary, from bend main.bend -o):
# BGZF output is refused before anything is written; plain output works.
if [ -n "$NOLIB" ]; then
  b7=0
  old $ex
  $NOLIB norm -c e -f data/chr22.fa -o $ex data/hg002.chr22.vcf > /dev/null 2> $D/new/f.err; e=$?
  [ $e = 2 ] && grep -qx "error: no BGZF in this build $ex" $D/new/f.err && [ "$(cat $ex)" = "old file" ] || { fail "no BGZF [-o]: exit $e"; b7=1; }
  $NOLIB norm -c e -f data/chr22.fa -Oz data/hg002.chr22.vcf > $D/new/nl.out 2> $D/new/f.err; e=$?
  [ $e = 2 ] && grep -qx "error: no BGZF in this build -" $D/new/f.err && [ ! -s $D/new/nl.out ] || { fail "no BGZF [-Oz]: exit $e"; b7=1; }
  $NOLIB norm -c e -f data/chr22.fa -o $D/new/nl.vcf data/hg002.chr22.vcf 2>/dev/null
  cmp -s $D/new/nl.vcf $D/ref/chr22.e.out || { fail "no BGZF build, plain -o"; b7=1; }
  [ $b7 = 0 ] && echo "NO-BGZF BUILD OK"
fi
[ $bad = 0 ] && echo "OUT OK" || echo "OUT FAILED"
exit "$bad"
