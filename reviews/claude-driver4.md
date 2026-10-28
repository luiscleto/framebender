# Driver review (`driver` branch): not accepted, one should-fix

One finding needs fixing first: a `.vcf.gz` cut exactly between two blocks is accepted without any error. The other three are minor. The repository is untouched; all test files are under `/tmp/fb_review*`, `/tmp/fbr_fz` and `/tmp/fbr_gz`.

## What I checked, and it held
- **FASTA fast path:** I compared it with main's build (`data/tmp/fb_c`) on 1,500 random cases. They covered line widths 15 to 70, CRLF, lower case, bytes ≥ 128, NUL and `>`, short last lines, damaged bytes, cut files and all three `-c` modes. Stdout, stderr and exit code were identical every time; 316 of those runs were driver errors. Each reference read takes whole lines, so the fast path really ran. A read at an offset past 5 GiB (sparse file) was also identical.
- **Read-ahead thread:**
  - Effects run on the event-loop thread with `ALC[0]`.
  - The heap grows in place: `corpus_grow` only maps more memory after it, and `corpus_lay` moves only the banks, which sit above every allocated page.
  - The runtime has no tracing garbage collector, `madvise`, atexit handler or destructor. So writing into a block that no term references yet is safe.
  - Every helper is joined by the next call and its duplicate descriptor closed.
  - On a slow pipe the process held a steady 8 descriptors and 3 threads.
  - Pipe, FIFO and `-c e` runs matched main's output; on the FIFO only the echoed path differs.
- **BGZF:** my own BGZF writer made 1,172 blocks, including 296 of 65,536 bytes and empty blocks in the middle. Its output matched the plain file exactly, with and without the end marker. Each damaged case gave `bad BGZF` with exit 2: a flipped CRC, ISIZE 65,537 or 65,535, BSIZE 24 or too long, a cut in the middle of a block, and trailing zeros. Plain gzip gave `unsupported gzip`. Zlib data that isn't gzip was read as text (`NO_HEADER`). No byte is handed out before its block's CRC passes.
- **Builds:** the one-step build gives `no BGZF in this build` on BGZF input and is identical to main on plain input. `build.sh` uses the same flags as `bend -o`.

## Findings
1. **Should fix: a `.vcf.gz` cut exactly at a block boundary is accepted silently.**
   - **Place:** `io64_block_in` and `io64_text` (`io64.c:179-241`). The end of the file at a block boundary always ends the stream.
   - **Input:** `/tmp/fbr_gz/cutblk.vcf.gz` (chr22 with its first 40% of blocks kept and no end marker). The run gives exit 0 and the summary line `framebender: 19422 records, ...` out of 50,284. This is a realistic case: a `bgzip` or `bcftools -Oz` writer that was killed leaves the file ending on a block boundary.
   - **Fix:** remember whether the last block decompressed to 0 bytes. At the end of the file, fail with `IO64_BAD_BGZF` if it didn't. bgzip and htslib always end a file with that empty block; htslib warns "EOF marker is absent" when it's missing. Add "and ending with the empty BGZF block" to the trust comment in `MACHINE.bend`, `docs/LAWS.md` and the `main.bend` header. Files written by very old tools (no end marker) would then be refused, and the user can run `bgzip -dc` first.
2. **Minor (older than this change; read-ahead adds one more block): on CPU builds the heap running out is never reported as `error: out of memory`.**
   - **Place:** `io64_block` (`io64.c:64`) relies on `err_seen`. In the generated C (`data/tmp/speed/fb.c:1682`) that is `DEVICE && ...`, which is always false on CPU.
   - **What happens:** `heap_alloc_miss` → `err_post` → `err_fail` → `_exit(1)`, printing "bend: out of memory: ...". The `main.bend` header and the note's "if no block is available, nothing is read ahead" are not true on CPU.
   - **Fix:** list this runtime stop (exit 1) in the trust comment, since the effect can't catch it.
3. **Minor: "any other gzip VCF is refused" is looser than the actual test, which is only the first two bytes `1f 8b`.**
   - **Input:** a 2-byte file `1f 8b`, or `1f 8b` followed by VCF text. These now get `unsupported gzip` with exit 2; main gave `NO_HEADER` with exit 1.
   - Refusing these is the right behaviour, which also answers the author's 4th question.
   - **Fix:** word the comment as "a VCF whose first two bytes are 1f 8b and that does not start with a BGZF block header is refused".
4. **Minor: `build.sh` always runs `clang`, while `bend -o` uses `$CC` when it is set.**
   - **Fix:** use `${CC:-clang}`.

## Author's questions
- **Helper writing into an unreferenced heap block:** safe under this runtime (reasons above).
- **Descriptor, device and inode as the stream identity:** enough for how the driver calls it. The `.fai` is closed before the FASTA and VCF are opened, so the VCF can never reuse the `.fai`'s descriptor with the same inode.
- **Header check:** stricter than htslib (FLG must be exactly FEXTRA), and that matches what bgzip writes.
- **Text VCF starting with `1f 8b`:** keep it an error; that's finding 3.

**Verdict: not ACCEPT yet. Fix 1; 2 to 4 are minor.**
