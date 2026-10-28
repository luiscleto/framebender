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
${CC:-clang} -std=c11 -O3 -DFB_LIBDEFLATE "$tmp/framebender.c" -lpthread -lm -ldeflate -o "$out"
