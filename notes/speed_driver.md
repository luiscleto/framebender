# Speed, steps 1 and 2: the driver (phase D, speed agent, 2026-10-28)

Plan: `notes/speed_plan.md` (options A1, A2 and B). Lead's decisions: pinned timings with the
unpinned ranges beside them; libdeflate linked by a two-step build, not vendored; BGZF only, any
other gzip refused with a message pointing to `gzip -dc ... | framebender ... /dev/stdin`; the
trust comment in `MACHINE.bend` goes to the driver review only; write-behind dropped.

Branch `driver`, not committed. Files: `io64.c`, `io64.js`, `main.bend`, `build.sh` (new),
`MACHINE.bend` (comments only), `docs/DEVELOPMENT.md`, `docs/LAWS.md`. Nothing in the laws, the
proofs, the machine or `../lawful-*` changed.

## Result

Whole genome (HG002, 4,048,342 records), `-c w`, interleaved rounds, wall clock. `main` is
`data/tmp/fb_c` (the current main build), `new` is `./build.sh`'s binary.

Pinned to the P-cores (`taskset -c 0-15`, both tools), 3 rounds each:

| input | output | main | new | bcftools 1.24 |
|---|---|---|---|---|
| plain VCF | file | 5.38-5.54 s | 4.84-4.99 s | 7.69-7.90 s |
| plain VCF | /dev/null | 4.90-5.14 s | 4.30-4.52 s | 5.38-5.77 s |
| `.vcf.gz` (BGZF) | file | 6.15-6.57 s (`bgzip -dc \| main /dev/stdin`) | 4.83-5.15 s | 7.91-8.08 s |
| `.vcf.gz` (BGZF) | /dev/null | 5.67-5.81 s (`bgzip -dc \|`) | 4.30-4.56 s | 5.79-6.03 s |

Unpinned, to a file, 5 rounds (before the BGZF end-of-member fix below, which touches no hot
path): main 5.91-7.94 s, new 5.75-6.38 s, bcftools 7.75-7.78 s. On `.vcf.gz`: `bgzip -dc | main`
7.41-10.27 s, new 5.37-6.57 s, bcftools 7.93-8.04 s.

chr22 and `scr.vcf` (pinned, 5 rounds) are unchanged: chr22 main 0.086-0.114 s, new 0.088-0.114 s,
new on a `.vcf.gz` 0.091-0.110 s, bcftools 0.107-0.111 s (0.114-0.126 s on the `.vcf.gz`); scr
main 0.110-0.126 s, new 0.105-0.123 s, bcftools 0.066-0.074 s.

## What changed

**A1, `Io.fa_read`** (`io64_line`). Before today's per-run test: when the column is 0,
`lw = lb + 1`, `16 <= lb <= 64`, the whole line and its LF are in the part read, and the letters fit
`want`, the line's `lb` bytes are tested with 16-byte SSE2 compares (no LF, CR, space or tab; the
last block ends at `lb` and may overlap the one before) and byte `lb` must be an LF. Then the
letters are copied and the LF skipped, exactly as the per-byte rule would take them. In every other
case nothing is taken and today's code runs, so the rule and the codes 0/1/2 are unchanged. Without
SSE2 (`#ifndef __SSE2__`) the path is never taken.

**A2, `Io.read_block` reads ahead.**
- After a full piece, the effect allocates the next piece's block (on the Bend thread) and starts
  a helper thread that reads into it, through a `dup` of the descriptor, which shares the file
  position. The next call joins the helper and hands that block out, then starts the next one.
- Errors are the same, at the same call: the helper's errno or BGZF code is returned by the call
  that hands its piece out.
- Heap blocks are allocated and freed only on the Bend thread. The block being filled is
  referenced by no term until it is handed out. If no descriptor or thread is available, nothing
  is read ahead and the next call reads the piece itself. A full heap is not seen by the effect on
  a CPU build: Bend's runtime stops the run first ("bend: out of memory: ...", exit code 1; see
  "After driver review 4").
- One stream at a time, known by its descriptor, device and inode: the `.fai` is read to its end
  before the VCF is opened. A call for another file while the last one still has bytes to hand out
  fails with EBUSY ("cannot read"); the driver never does that. A call with another `max` than the
  piece read ahead fails with EINVAL; the driver always asks `piece()`.
- At an early `Finish` (`-c e`) the helper may still be reading when the process exits. That is
  harmless: its descriptor is its own, and its block is never used.

**B, BGZF input.**
- `Io.read_block(file, max, gz)` gets a third argument: 1 for the VCF, 0 for the `.fai`, which is
  always read as bytes.
- With gz = 1 the first 18 bytes are read to learn the format; they are handed out as text if the
  file is plain. This works on pipes too (no seek).
  - The file starts with `1f 8b` and a BGZF block header (the fixed header htslib checks: FLG =
    FEXTRA only, XLEN = 6, subfield `BC` of length 2): each block is decompressed with libdeflate.
    A block goes straight into the piece when it fits, else into a 64 KB carry buffer handed out by
    the next calls. Each block needs exactly its header, BSIZE >= 25, the whole block present, the
    deflate data using exactly all of its bytes, ISIZE <= 65536 and equal to what came out, and the
    CRC32. Empty blocks (bgzip's end marker, also found between concatenated members) give no text
    and do not end the stream; only the end of the file does, and it must come right after an
    empty block (added after driver review 4).
  - The first two bytes are `1f 8b` and no BGZF block header follows: fails, "unsupported
    gzip".
  - Anything else: plain bytes, as before.
- Decompression runs in the read-ahead helper, so it overlaps the machine. One libdeflate thread
  decompresses this file at about 5.4 GB/s; the machine consumes 0.65 GB/s.
- New errors (exit code 2, one line on stderr; the effect's codes 1001-1003, mapped in
  `main.bend`'s `read_fail`):
  - `error: unsupported gzip <path> (not BGZF; use gzip -dc <path> | framebender ... /dev/stdin)`
  - `error: bad BGZF <path>`: a damaged or cut block, or no empty block at the end of the file
  - `error: no BGZF in this build <path>`: a binary built without libdeflate
- **Build.** `build.sh`: `bend main.bend -o <tmp>/framebender.c`, then
  `${CC:-clang} -std=c11 -O3 -DFB_LIBDEFLATE <tmp>/framebender.c -lpthread -lm -ldeflate` (what `bend -o`
  runs, plus libdeflate). The libdeflate code is under `#ifdef FB_LIBDEFLATE`, so
  `bend main.bend -o framebender` still builds, and that binary stops on a BGZF VCF with the third
  error. `docs/DEVELOPMENT.md` says so; **the README's install line (`bend main.bend -o
  framebender`) and its `.vcf.gz` hint are the lead's to update.**
- Trust boundary: `MACHINE.bend`'s list of what the law does not cover now says that for a BGZF
  VCF the bytes read are the decompressed ones, with each block's CRC32 and length checked, and
  that other gzip is refused. It also lists the three new errors. `docs/LAWS.md`, "What the laws do
  not cover", says the same.

## Checks (all on the final build)

- `test/same.sh <new> data/tmp/fb_c`: ALL IDENTICAL (128 runs) for `./build.sh`'s binary, for a
  one-step `bend -o` build, and for two test builds with `piece()` = 70,001 and 1,000 bytes. Those
  two exercise the carry buffer, blocks split across pieces and many read-aheads. The cache of
  reference results `data/tmp/rw/ref` had been made with `data/tmp/fb_ref`; it is kept as
  `data/tmp/rw/ref.fb_ref` and was remade with `fb_c`.
- `data/tmp/speed/gztest.sh` (for the same three builds; 756 comparisons, ALL IDENTICAL). Every
  input of `same.sh` (edge, chr22, scr, `edge2`, `rw`) and five concatenated-member files (members
  ending mid-piece, exactly at a piece boundary for each piece size, and three empty members in a
  row), under `-c e` and `-c w`:
  1. the plain file, against `fb_c`;
  2. a bgzipped copy at the same relative path (so the echoed command line is the same), against
     (1);
  3. the bgzipped copy through a pipe (`cat | ... /dev/stdin`), against `fb_c` on the plain file
     through a pipe.
- Whole genome, `-c w` and `-c e`: stdout, stderr and exit code identical to `fb_c` on the plain
  file, both for the plain file and for the GIAB `.vcf.gz` (same relative path).
- `test/compare.sh` with the new binary: chr22 0, scr 0, `test/edge/sorted.vcf` 1 (the `<DEL>`
  record), whole genome 0, whole genome from the `.vcf.gz` 0.
- Damaged input (chr22 bgzipped): cut in half, one bit flipped in deflate data, `BC` changed,
  BSIZE zeroed, ISIZE changed, a plain gzip member after the BGZF ones: each `error: bad BGZF
  <path>`, exit 2. Plain gzip and a 3-byte `1f 8b 08` file: `unsupported gzip`. An empty BGZF
  file: `NO_HEADER`, as an empty plain file. A directory as the VCF: `cannot read`, as before.
  A one-step build on a `.vcf.gz`: `no BGZF in this build`.
- The gate, each step through `test/bcheck.sh`: `examples.bend` (its 15 TODOs, as before),
  `main.bend` (62 defs rely on unsafe or foreign code, the same count as before the change),
  `PROOF.bend --check-only` and `--verdict`: ALL PROOFS CHECK. `MACHINE.bend --check-only`: its
  15 TODOs, as before.

## A bug the tests caught on the way (research data)

The first BGZF reader treated a block that decompresses to nothing as the end of the file. bgzip
ends every file with such a block, so in a concatenation of bgzipped files it also sits between
members. When it came first in a piece, the piece was empty and the driver took that as the end of
the VCF. The run stopped early, silently, with exit code 0: 24,385 of chr22's 50,284 records, on a
file whose first member ended exactly at a piece boundary. The first test round missed it (its
member boundary fell mid-piece). Reading the diff before the report found it, and a piece-aligned
test reproduced it. Now only the end of the file ends the stream, and the test set has four
piece-aligned and empty-member cases. A law-checked machine would not have helped: this is in the
trusted driver, which the law takes on trust.

## After driver review 4

Reviews: `reviews/*-driver4.md`, the lead's verdicts in `reviews/responses-driver4.md`. GPT and Grok
accepted; Claude found one should-fix and three minor issues, all confirmed by the lead. Fixed on
branch `driver`, not committed:

1. **A `.vcf.gz` cut exactly at a block boundary was accepted** (exit 0, 19,422 of chr22's 50,284
   records on the reviewer's `/tmp/fbr_gz/cutblk.vcf.gz`). A killed `bgzip` or `bcftools -Oz`
   leaves such a file. The stream (`Io64In`) now remembers whether its last block was empty
   (`last0`); the end of the file without an empty block just before it fails with
   `IO64_BAD_BGZF`, so the run stops with `error: bad BGZF <path>`, exit 2. The bytes of the piece
   holding the end are never handed out, so nothing more is written. bgzip and htslib end every
   file with that block; a file from a tool that writes none is refused (`bgzip -dc` first). Said
   in `io64.c`, the `main.bend` header, the trust comment in `MACHINE.bend` and `docs/LAWS.md`.
   The same kind of bug as the one above (an early end of the stream that exits 0), in a case none
   of my tests reached: they cut only inside a block.
2. **Out of memory on a CPU build.** `io64_block` tests `err_seen`, which is
   `DEVICE && ...`, false on CPU: a full heap stops the run inside the runtime (`heap_alloc_miss`,
   `err_fail`: "bend: out of memory: ...", exit 1) before the effect sees it. This is older than
   this change. The comments no longer claim the driver reports a full heap as `error: out of
   memory`: that error now names only a read's buffer and libdeflate's decompressor (`malloc`),
   and the runtime stop lists the blocks the driver allocates (`main.bend` header, `MACHINE.bend`
   trust comment, `io64.c`). The checks in the code stay (true on device builds).
3. **"Any other gzip VCF is refused"** now says what is tested: a VCF whose first two bytes are
   `1f 8b` and that does not start with a BGZF block header (`MACHINE.bend`, `docs/LAWS.md`, the
   `main.bend` header, `io64.c`). The behaviour is kept.
4. **`build.sh`** runs `${CC:-clang}`, as `bend -o` does. `CC=gcc ./build.sh` builds and passes the
   checks below.

Checks after the fixes, on fresh builds (`./build.sh`, `CC=gcc ./build.sh`, a one-step
`bend -o`, `piece()` = 70,001 and 1,000):
- `test/same.sh <bin> data/tmp/fb_c`: ALL IDENTICAL (128 runs) for each of the five builds.
- `data/tmp/speed/gztest.sh` on the four libdeflate builds: ALL IDENTICAL (1,008 comparisons).
  This covers files with the end block and concatenated members whose own end blocks sit in the
  middle.
- `data/tmp/speed/eoftest.sh` (new) on the same four builds: ALL AS EXPECTED (240 runs). Files
  without the end block, each run on a file and through a pipe, under `-c e` and `-c w`:
  - chr22 cut after blocks 1, 25, 217, 400 and 542 of its 543, and after 543 (the end block
    removed). 25 blocks are exactly 1,632 pieces of 1,000 bytes, so on that build the read-ahead
    meets the end.
  - Members cut at a piece boundary of each build (11,010,048, 7,000,100 and 17,000,000 bytes),
    their end block removed.
  - Two concatenated members: the last end block removed, and a cut just before the middle one.
  - Every edge file, its end block removed.

  Each must give exit 2 and the last stderr line `error: bad BGZF <path>`. Its stdout must be a
  prefix of `fb_c`'s on the whole plain file, and its stderr, without that line, a prefix of
  `fb_c`'s. Two files that do end with the block must match `fb_c` on the same text: the two
  members cut right after the middle end block, and a file that is only the end block (as an
  empty plain file: `NO_HEADER`).
  The build before the fix (`data/tmp/fb_d`) fails 128 of these checks. On the reviewer's file it
  gives exit 0 and 19,422 records; the new build gives exit 2 and `bad BGZF` after 15,617
  records.
- Damaged files (`bad/`), unchanged: each gives `bad BGZF`, `unsupported gzip` or `NO_HEADER`, as
  before. A one-step build on a `.vcf.gz`: `no BGZF in this build`.
- Whole genome, `-c w` and `-c e`: stdout (2,836,801,738 bytes), stderr and exit code identical
  to `fb_c` on the plain file, both for the plain file and for the GIAB `.vcf.gz`. That file ends
  with the end block (28 bytes, ISIZE 0).
- `test/compare.sh`: chr22 0, scr 0, `test/edge/sorted.vcf` 1 (the `<DEL>` record), whole genome
  0, whole genome from the `.vcf.gz` 0.
- The gate, each step through `test/bcheck.sh`: `examples.bend` 15 TODOs, `main.bend` 62 defs
  rely on unsafe or foreign code, `PROOF.bend --check-only` and `--verdict` ALL PROOFS CHECK,
  `MACHINE.bend` 15 TODOs. All as before.
- Not re-timed: the change adds one test per BGZF block and one at the end.

## For the driver review

- `io64.c`: the BGZF reader (`io64_kind`, `io64_block_in`, `io64_text`), the read-ahead
  (`io64_ahead_*`, `io64_piece`, `io_read_block_run`), the whole-line path (`io64_line` and its
  call in `io_fa_read_run`).
- `main.bend`: the third argument of `Io.read_block`, `read_fail`'s new messages, the header
  comment. `io64.js`: the stub's new argument.
- `build.sh`, and the trust sentences in `MACHINE.bend` and `docs/LAWS.md`.
- Runtime internals newly used: none (`heap_alloc`/`heap_free` via `io64_block`, `blk_wcls`,
  `term_blk`, `io_tup`, `io_done`, `io_fail`, `io_hand`, `io_hand_v`, as before).
- Questions worth the reviewers' time:
  - Is a helper thread writing into a heap block that no term references yet safe under Bend
    2.0.39's runtime (no moving, no reuse before it is handed out)?
  - Is the stream identity (descriptor, device, inode) enough?
  - Is the BGZF header check strict enough, and not too strict for real files? It accepts what
    htslib accepts.
  - Should a VCF whose first bytes are `1f 8b` but that the user meant as text be an error? The
    spec would have read it as text and stopped with `NO_HEADER`.

## Scratch (`data/tmp/speed`)

`gztest.sh` (the BGZF comparisons), `eoftest.sh` and `eof/` (files without the end block; the
block list from `tools/blocks.py`), `bench4.sh` (the timings above), `bad/` (the damaged
files), `cat2/` (the piece-aligned reproduction), `fb_drv*` (the builds checked).
