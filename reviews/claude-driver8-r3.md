## Driver review 8, round 3: ACCEPT

Decisions 8–10 are fixed, and I found no new problem. I tested a fresh `./build.sh` of the current tree. The reproduction scripts are in `/tmp/claude-1000/-home-luisc-Work-bend-projects-framebender-gz/344bf104-98d7-45c9-8322-c56328d2dcf7/scratchpad/fb8/`.

**Decision 8, the take-back through a duplicate descriptor (`io64_out_open`, `io_out_close_run`)**
- **Code:**
  - The duplicate is taken with `F_DUPFD_CLOEXEC` at descriptor 3 or above, before `ftruncate`, and only for a regular `-o` file. If it can't be had, the open fails like any other.
  - After a failed `close`, the end-of-file block is truncated away through the duplicate: the same open file, with no lookup by path.
  - The duplicate is closed after the file. Not reporting an error from that second close is sound: Linux runs the flush on the first `close` of the shared file, and a writeback error is reported once per open file.
  - The duplicate is cleared on every path. Plain output and FIFOs never take a duplicate, since `at` stays -1 for them.
- **Re-pointed path:** I injected `EIO` into `close` and, in the same shim, moved the file away and pointed its path at another file. The run exits 2 with "cannot write <path>". The other file is unchanged, and the moved file is bgzip's bytes less the end-of-file block.
- **umask 0777:** the run exits 2, and the file is bgzip's bytes less the end-of-file block. The take-back is now exact, so the comments rightly no longer say "best effort".
- **Successful close:** a shim on another path leaves the file complete and identical to bgzip's output, exit 0.

**Decision 9, stderr compared only when it is a regular file**
- `-o /dev/stdout 2>&1 | tail` now runs, as do `-o -` and plain stdout with the same redirection.
- `-o /dev/stderr` with stderr a FIFO runs, exit 0, with the output and the messages on the FIFO.
- `-o err.txt 2> err.txt` is still refused ("output is an input").

**Decision 10, the tests**
- `out.sh`'s `write()` shim does what decision 10 asks: it fails the k-th output write once with `EIO` and lets later writes through.
- **My own shim:**
  - BGZF, third write: exit 2, "cannot write", a non-empty prefix of bgzip's bytes, no end-of-file block.
  - Plain, k = 2: exit 2, a prefix.
  - Plain, k = 3: the run exited 0 with the file complete. This is not a bug: that small run makes only two plain writes, so the third never happens. `out.sh` uses chr22, which makes many.
- `gen_out.py` now says that `tailwin` can't tell the uncut end from cutting again. Skipping the direct C test of the cut is acceptable, since a text without a final LF can't come from the machine.

**Earlier reproductions, re-run:** all still pass.
- **Inputs:** a pipe VCF with `-o /dev/stdin`, and one FIFO as both VCF and `-o`, are refused with no hang.
- **Byte identity:** matches `bgzip -l L`
  - at levels 0–9 on `sorted.vcf`;
  - on a header-only file;
  - on `tailwin`, whose text is exactly 65,280 bytes;
  - on every `gen_out.py` case at levels 0, 6 and 9 with `--threads` 1 and 128.
- **Close failure without re-pointing:** the end-of-file block is taken back.
- **File size limit with no trap:** exit 2, "cannot write <path>", the file stopped at the limit, no end-of-file block. A BGZF run that fits under its limit exits 0, which is correct.

**Comments:** law machine's comment and `docs/LAWS.md` describe the take-back through the duplicate and say a pipe can't take it back.
