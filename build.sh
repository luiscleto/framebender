#!/bin/sh
# Builds framebender in two steps: bend writes the program as C (main.bend,
# with the driver's effects from io64.c), then clang compiles it the way
# `bend -o` does (with $CC if set, else clang), adding libdeflate, which reads
# BGZF (.vcf.gz) input.
#   ./build.sh [output]        (default: framebender next to this script)
# A plain `bend main.bend -o framebender` still builds; that binary stops on a
# BGZF VCF with "error: no BGZF in this build <path>".
# The index (-W) needs htslib 1.24 built without libcurl, GCS and S3
# (tools/build_htslib.sh installs it in ~/.local/opt/htslib-1.24-nocurl),
# found by pkg-config (PKG_CONFIG_PATH, default that prefix) and linked
# statically: its tbx_parse1 and hts_adjust_csi_settings are not exported by
# libhts.so. FB_NO_HTSLIB=1 builds without it; -W then stops with "error: no
# index in this build <path>".
set -e
here=$(dirname "$0")
out=${1:-$here/framebender}
export BEND_NO_TELEMETRY=1
hts=
if [ "${FB_NO_HTSLIB:-0}" != 1 ]; then
  pfx=$HOME/.local/opt/htslib-1.24-nocurl
  export PKG_CONFIG_PATH=${PKG_CONFIG_PATH:-$pfx/lib/pkgconfig}
  need="-W needs htslib 1.24 built without libcurl: tools/build_htslib.sh installs it in $pfx (./configure --disable-libcurl --disable-gcs --disable-s3), found with PKG_CONFIG_PATH=$pfx/lib/pkgconfig; FB_NO_HTSLIB=1 builds without -W"
  [ "$(pkg-config --modversion htslib 2>/dev/null)" = 1.24 ] || { echo "build.sh: no htslib 1.24 found by pkg-config. $need" >&2; exit 1; }
  lib=$(pkg-config --variable=libdir htslib)/libhts.a
  libs=$(pkg-config --variable=static_libs htslib)
  case " $libs " in *" -lcurl "*) echo "build.sh: $lib is built with libcurl. $need" >&2; exit 1 ;; esac
  for f in tbx_parse1 hts_adjust_csi_settings; do
    nm "$lib" 2>/dev/null | grep -q " T $f\$" || { echo "build.sh: $lib does not define $f. $need" >&2; exit 1; }
  done
  hts="-DFB_HTSLIB $(pkg-config --cflags htslib) $lib $libs"
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bend "$here/main.bend" -o "$tmp/framebender.c"
# The runtime patch (notes/memory.md): a freed heap block of 256 KiB or more
# (a class whose keep limit is one block) goes straight to the shared bank,
# instead of staying parked on the thread that freed it, where the main
# thread, which allocates every piece and window, never reuses it. Written
# for Bend 2.0.39's runtime: the build stops if the code it relies on is not
# exactly as expected.
c=$tmp/framebender.c
awk '/^OUTLINE void heap_hand\(Env e, u32 cls\) \{$/,/^}$/' "$c" > "$tmp/hand.c"
cat > "$tmp/hand.want" <<'EOF'
OUTLINE void heap_hand(Env e, u32 cls) {
  u64 cold = ALC_COLD(e, cls);
  if (cold) {
    bank_push(e.mem, cls, cold);
  }
  ALC_COLD(e, cls) = ALC_AT(e, cls);
  ALC_AT(e, cls)   = ALC_LEN(e, cls) = 0;
}
EOF
# Each line below exactly once; each macro below defined once (no second
# definition after an #undef); heap_hand named twice in all: its definition
# and the call in heap_free.
one() { [ "$(grep -c -x -F "$1" "$c")" = 1 ]; }
def() { [ "$(grep -c -E "^[[:space:]]*#[[:space:]]*define[[:space:]]+$1([[:space:](]|$)" "$c")" = 1 ]; }
quantum='#define QUANTUM   (DEVICE ? PAGE_LEN \
  : KEEP_WORDS < 32 * PAGE_LEN ? KEEP_WORDS : 32 * PAGE_LEN)'
if ! cmp -s "$tmp/hand.c" "$tmp/hand.want" \
  || ! one '#define KEEP(c)        (KEEP_WORDS >> (c) ? KEEP_WORDS >> (c) : 1)' || ! def KEEP \
  || ! one '#define NCLS      8' || ! def NCLS \
  || ! one '#define CAP_WORDS 32768' || ! def CAP_WORDS \
  || ! one '#define CHUNK     256' || ! def CHUNK \
  || ! one '#define QUANTUM   (DEVICE ? PAGE_LEN \' || ! def QUANTUM \
  || [ "$(grep -x -F -A1 '#define QUANTUM   (DEVICE ? PAGE_LEN \' "$c")" != "$quantum" ] \
  || ! one '  KEEP_WORDS = gpu ? CHUNK : CAP_WORDS;' \
  || ! one '  u32 n = got ? KEEP(cls) : cls < NCLS ? QUANTUM >> cls : 1;' \
  || ! one '  if (!DEVICE && ALC_LEN(e, cls) >= KEEP_WORDS) {' \
  || ! one '    heap_hand(e, cls);' \
  || [ "$(grep -o 'heap_hand' "$c" | wc -l)" != 2 ]; then
  echo "build.sh: the generated runtime is not the one the heap patch was written for (Bend 2.0.39); see notes/memory.md" >&2
  exit 1
fi
awk '{ print }
/^OUTLINE void heap_hand\(Env e, u32 cls\) \{$/ {
  print "  if (KEEP(cls) == 1) {"
  print "    bank_push(e.mem, cls, ALC_AT(e, cls));"
  print "    ALC_AT(e, cls) = ALC_LEN(e, cls) = 0;"
  print "    return;"
  print "  }"
}' "$c" > "$tmp/patched.c"
${CC:-clang} -std=c11 -O3 -DFB_LIBDEFLATE "$tmp/patched.c" $hts -lpthread -lm -ldeflate -o "$out"
