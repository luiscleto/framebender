# Driver review, round 2: ACCEPT

All four fixes are correct, and I found no regressions on valid files. The repository is as I found it (only the author's uncommitted changes); my test files are under `/tmp/fbr_gz2`, `/tmp/fbr_gz` and `/tmp/fbr_fz`.

## Finding 1: a file must end with the empty end-of-file block
**From the code:**
- `last0` is set from every block read, and reset whenever the stream's format is detected, so also for a new stream.
- `io64_block_in` is the only place a BGZF stream can end, and it now refuses an end that doesn't follow an empty block.
- On the read-ahead path the error comes back with the piece that holds the end. The bytes of that piece are dropped, so nothing past the cut is written.

**Tested on fresh builds:**

| Case | Result |
|---|---|
| A cut at each of the 543 block boundaries of a real `bgzip` chr22 (60 of them also through a pipe) | All 602 runs: exit 2, last line `error: bad BGZF`, stdout a prefix of main's plain run |
| End block removed, after one or more members | exit 2, `bad BGZF` |
| End block cut short by 1, 14 or 27 bytes | exit 2, `bad BGZF` |
| Two full pieces of text (2 × 3,670,016 bytes) with no end block, so the read-ahead meets the end | exit 2, `bad BGZF` |
| Round-1 files: `cutblk`, `noeof`, bad CRC, ISIZE 65,535 and 65,537, BSIZE 24 and too long, trailing zeros, a cut mid-block | exit 2, `bad BGZF` |
| Plain gzip | `unsupported gzip` |
| Zlib data that isn't gzip | read as text: `NO_HEADER`, as main |

**Valid files are unchanged** (stdout, stderr and exit code identical to main on the same text, under `-c w` and `-c e`):
- a real `bgzip` file;
- two members concatenated;
- members with extra empty blocks before, between and after them;
- two members with the middle end block removed;
- a file of exactly two pieces of text;
- a file that is only the end block, or two of them (`NO_HEADER`, like an empty plain file).

**One way a cut file still exits 0:** a concatenated file cut exactly after a middle member's end block. It's a valid BGZF file holding fewer members, so nothing can tell it apart; htslib accepts it too. No change needed.

## Findings 2 to 4
- **2.** The out-of-memory comments are now accurate in `MACHINE.bend`, the `main.bend` header and `io64.c`. `error: out of memory` now covers only a `malloc` buffer and libdeflate's decompressor, and the runtime's own stop (exit 1) is listed.
- **3.** The comments now say what is actually tested: the first two bytes are `1f 8b` and no BGZF block header follows. The behaviour is unchanged.
- **4.** `build.sh` runs `${CC:-clang}`.

## Regressions
- The one-step `bend -o` build gives `no BGZF in this build` on a `.vcf.gz` and is identical to main on plain input.
- The FASTA comparison against main (300 new random cases) gave no differences.

**ACCEPT.**
