#!/bin/sh
# Builds framebender in two steps: bend writes the program as C (main.bend,
# with the driver's effects from io64.c), then clang compiles it the way
# `bend -o` does (with $CC if set, else clang), adding libdeflate, which reads
# BGZF (.vcf.gz) input.
#   ./build.sh [output]        (default: framebender next to this script)
# A plain `bend main.bend -o framebender` still builds; that binary stops on a
# BGZF VCF with "error: no BGZF in this build <path>".
set -e
here=$(dirname "$0")
out=${1:-$here/framebender}
export BEND_NO_TELEMETRY=1
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
one() { [ "$(grep -c -x -F "$1" "$c")" = 1 ]; }
if ! cmp -s "$tmp/hand.c" "$tmp/hand.want" \
  || ! one '#define KEEP(c)        (KEEP_WORDS >> (c) ? KEEP_WORDS >> (c) : 1)' \
  || ! one '  u32 n = got ? KEEP(cls) : cls < NCLS ? QUANTUM >> cls : 1;' \
  || ! one '  if (!DEVICE && ALC_LEN(e, cls) >= KEEP_WORDS) {'; then
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
${CC:-clang} -std=c11 -O3 -DFB_LIBDEFLATE "$tmp/patched.c" -lpthread -lm -ldeflate -o "$out"
