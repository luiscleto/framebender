# Driver review 8 (branch `gz`, uncommitted): compressed output

## Context
I'm doing the review `reviews/DRIVER8_PROMPT.md` asks for: the trusted driver's new output path (`io64.c` output
section, stream identities, constructor grammar; `main.bend` plumbing; `io64.js`; `test/out.sh`,
`test/gen_out.py`). Read so far (plan mode, so nothing built or run yet): `git diff` of io64.c,
main.bend, types.bend, MACHINE.bend, io64.js; notes/compress.md "The driver" and "Step 2";
htslib 1.24 `bgzip.c` text mode (data/tmp/gz/src/bgzip.c); Bend's generated `io_cbuf`.

## Remaining step after approval (read-only for the repo; scratch under /tmp only)
1. `./build.sh /tmp/fb8/fb`
2. Finding 1: `cat test/edge/sorted.vcf | /tmp/fb8/fb norm -f test/edge/ref.fa -o /dev/stdin /dev/stdin`
   (under `timeout 20`) and the named-FIFO form (`mkfifo /tmp/fb8/p; cat test/edge/sorted.vcf > /tmp/fb8/p &
   fb norm -f test/edge/ref.fa -o /tmp/fb8/p /tmp/fb8/p`). Expected today: no refusal, a hang or a garbled run.
3. Finding 2: a small python VCF in /tmp whose output is a 60000-byte header + records, no final LF, and
   exactly 65280 bytes in all (if the machine keeps the missing LF), then `cmp` with `bgzip -l 6`. If the
   machine always adds the LF, finding 2 is unreachable, and I'll call it a comment fix.
4. Adjust the severities from what runs, then give the final report below.

## Report (draft, from reading)

Verified as correct: the ring, the compressors and the writer (one mutex, a broadcast on every state
change, no lost wake-up; `out_write` drains before it frees the buffer, so no thread touches
the heap and none is mid-write at any `die`/exit); the carried tail (no loss or duplication, `cs ≥ ws`,
copy bounds); CRC32/ISIZE/BSIZE; a stored-block fallback that can never trigger at 65280 bytes; level 0
as htslib writes it; the level map {0,1,2,3,5,6,7,8,10,12}; the end-of-file block only on code 0 with no
error, after the join; the sticky first error; the memory bound (limit × 64 KiB plus 2–3 window copies
per call); the identity check before `ftruncate` for regular files; the constructor's grammar, which matches
`Args.word`/`Args.step` branch for branch (and only sets Bend's worker count, not the output);
`main.k`'s `None` turns into an internal error; `io64.js`.

1. **should fix:** `io64.c`, `io64_out_open`. A FIFO or pipe input named as `-o` is not refused,
   because only `S_ISREG` files are compared. Trigger: `cat in.vcf | fb norm -f r.fa -o /dev/stdin /dev/stdin`
   (or `/proc/self/fd/0`, or a named FIFO given as both VCF and `-o`). The open gives the input
   pipe's write end, the output is fed back into the VCF stream, and the driver holds a write end. So
   the read never sees EOF: the run hangs, or the machine reads its own output. Fix: compare
   (dev, ino) with `io64_seen` and the FASTA for FIFOs and sockets as well as regular files. Compare with
   stderr for regular files only, and `ftruncate` only regular files. Add both triggers to out.sh §3.
2. **minor:** `io64.c`, `io64_out_tail`. When the last full window ends exactly at the end of the text,
   bgzip 1.24 writes the bytes carried after its cut as one block (the trailing `bgzf_write`, with no
   cut). `io64_out_tail` cuts them again. The block counts differ only if those bytes hold an LF and
   don't end with one: a header-mode cut followed by records, with no final LF. That is unreachable if the
   machine always ends its text with an LF, but the comment claims bgzip's bytes for any text. Fix:
   remember that no byte arrived after the last full window and queue `[cs, ps)` uncut, or narrow the
   comment.
3. **minor (comment):** `MACHINE.bend`, law machine, "Decompressed, the file is the output bytes
   written so far". After a driver error (`die`), the carried bytes (up to 65279) are never
   written. The BGZF file then decompresses to a strict prefix, while plain output has every byte. Say
   "a prefix of them (all of them when the machine finished)".
4. **minor (tests):** test/out.sh doesn't test the promises below:
   - "Nothing after a failed write": `/dev/full` and `--fsize` fail every later write too, so a writer
     that went on after the first error would still pass. Use a transient failure instead (stdout a
     non-blocking pipe whose reader pauses, giving EAGAIN once), then check that what arrives is a prefix
     of bgzip's bytes.
   - Identity by `/dev/stdin` and `/proc/self/fd/0` (with stdin the VCF), and by a FIFO input.
   - §6 (threads seen) asserts nothing, so the constructor's `-o`/`-O` grammar has no failing check.
   - "no BGZF in this build" for output (a plain `bend main.bend -o` build) is not run.

Verdict: not ACCEPT, because of item 1. Items 2–4 are minor.
