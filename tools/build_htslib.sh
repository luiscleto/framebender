#!/bin/sh
# Builds and installs the htslib that build.sh links for -W (phase J): htslib
# 1.24, static, without libcurl, GCS and S3, so that the binary does not pull
# in libcurl and libcrypto and htslib never opens a URL.
#   tools/build_htslib.sh [PREFIX] [TARBALL]
# PREFIX defaults to ~/.local/opt/htslib-1.24-nocurl; TARBALL to a download of
# the 1.24 release, checked against its SHA-256. Then build with
#   PKG_CONFIG_PATH=PREFIX/lib/pkgconfig ./build.sh
set -e
prefix=${1:-$HOME/.local/opt/htslib-1.24-nocurl}
tarball=$2
sum=28a8de191381c7a97a35675ceac76fa1ea95e7b678d6a2e9d600a7874e4077de
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
if [ -z "$tarball" ]; then
  tarball=$tmp/htslib-1.24.tar.bz2
  curl --proto '=https' --tlsv1.2 -fsSL -o "$tarball" https://github.com/samtools/htslib/releases/download/1.24/htslib-1.24.tar.bz2
fi
if command -v sha256sum > /dev/null; then got=$(sha256sum < "$tarball"); else got=$(shasum -a 256 < "$tarball"); fi
[ "${got%% *}" = "$sum" ] || { echo "build_htslib.sh: $tarball is not htslib 1.24's release (SHA-256)" >&2; exit 1; }
tar -xjf "$tarball" -C "$tmp"
cd "$tmp/htslib-1.24"
./configure --prefix="$prefix" --disable-libcurl --disable-gcs --disable-s3 --with-libdeflate > "$tmp/configure.log" 2>&1 \
  || { cat "$tmp/configure.log" >&2; exit 1; }
make -j"$(nproc 2>/dev/null || echo 4)" > "$tmp/make.log" 2>&1 || { tail -20 "$tmp/make.log" >&2; exit 1; }
make install > "$tmp/install.log" 2>&1 || { tail -20 "$tmp/install.log" >&2; exit 1; }
echo "htslib 1.24 (no libcurl) in $prefix: PKG_CONFIG_PATH=$prefix/lib/pkgconfig ./build.sh"
