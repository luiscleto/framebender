Review of framebender's trusted driver on the git branch `driver` (read-only: do not modify, create
or delete files in the repository, and do not switch branches).

framebender's program is proven: `PROOF.bend` proves every law of `LAWS.bend` and `MACHINE.bend`.
What the proof does not cover is the trusted driver, `main.bend` (Bend: the loop, `.fai` parsing,
answering reference reads) and `io64.c` (C effects). The comment above `law machine` in
`MACHINE.bend` lists exactly what the driver must do:
- read the files' bytes, one character per byte. For a VCF that is BGZF (`.vcf.gz`), the bytes
  its blocks decompress to, with each block's CRC32 and length checked; any other gzip VCF is
  refused;
- hand each VCF piece to the program as exactly `E.enc` of its text: bytes four to a word,
  little-endian, zero-padded, in the smallest perfect block that holds them, with pieces of at
  most 2^31 bytes;
- answer each reference read `Req{chrom, a, b}` of an `Ask`, in order, with exactly
  `truth(B.Fasta.parse(fasta), chrom, a, b)`, packed by `E.enc`, reading through the `.fai` index
  at 64-bit offsets;
- answer `P.Ask{[]}` as an ordinary step;
- write exactly the bytes of each output buffer and every message, then exit with the code;
- report its own errors, each as one line on stderr with exit code 2.

The previous driver was reviewed and accepted. This change makes it faster and adds `.vcf.gz`:
`git diff main -- main.bend io64.c io64.js build.sh MACHINE.bend` shows all of it, and
`notes/speed_driver.md` explains it (its last section lists the author's own open questions).
In short:
1. FASTA reads: a fast path for whole sequence lines (SSE2), falling back to the old
   byte-by-byte rule for anything unusual.
2. VCF reads: a helper thread reads the next piece ahead, into a block allocated on the main
   thread, through its own duplicate of the file descriptor.
3. BGZF: decompressed with libdeflate; other gzip is refused; three new driver errors.
4. `build.sh`: `bend main.bend -o x.c`, then clang with `-ldeflate`.

Check the new driver against that comment. Is there any way it does something other than what the
comment says? Look for, among others:
- the fast FASTA path answering anything different from the byte-by-byte rule (line lengths,
  the last line of a contig, CR, lower case, bytes >= 128, a read ending mid-line, offsets of
  4 GiB or more);
- the read-ahead thread: a race with the main thread or Bend's runtime (allocation, the heap,
  garbage), a piece delivered twice, out of order or lost, an error or EOF reported for the
  wrong piece, a short read, EINTR, a thread or descriptor leaked, behaviour on a pipe
  (`/dev/stdin`) or a FIFO;
- BGZF: a damaged or truncated file accepted, or its bytes passed on before its CRC is checked;
  a header that is not BGZF accepted; empty blocks and concatenated files; a block or `BSIZE`
  that overflows a size or a buffer; `ISIZE` larger than 64 KiB; a gzip VCF read as text, or a
  plain VCF that starts with gzip's magic bytes;
- memory errors in the C code: bounds, `malloc` failure, integer overflow in sizes;
- a message lost, or a wrong exit code; the one-step build (`bend main.bend -o`) and `build.sh`
  behaving differently other than the stated "no BGZF in this build" error.

You may build and run it on small inputs (`./build.sh /tmp/fb_review`, then
`/tmp/fb_review norm -f test/edge/ref.fa test/edge/sorted.vcf`; `bgzip` is installed), and you
may write test files under `/tmp` only.

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
