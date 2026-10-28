Review of framebender's trusted driver on the git branch `driver2` (read-only: do not modify, create
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

The previous driver was reviewed and accepted. The machine now judges batches of 16 VCF pieces in
parallel (proven), so one `Ask` can carry many reads. This change makes the driver keep up:
`git diff parallel -- main.bend io64.c io64.js` shows all of it, and `notes/speed_driver2.md`
explains it (its section "Open questions for the reviewers" lists the author's own doubts;
answer each). In short:
1. Reference reads: an `Ask`'s reads are started in groups of up to 32, each on its own thread
   (`Io.fa_start`), and collected in order (`Io.fa_wait`); the old `Io.fa_read` is removed.
   Read buffers are 1 MiB instead of 16 MiB.
2. VCF reads: the one-piece read-ahead becomes a queue of up to 16 pieces, filled in order by
   the same single helper thread, into blocks allocated on the main thread; when the heap cannot
   give a block, the main thread reads the piece itself.

Check the new driver against that comment. Is there any way it does something other than what the
comment says? Look for, among others:
- reference answers: one delivered to the wrong request, out of order, or computed differently
  from the old byte-by-byte rule; the first error in order not being the one reported (two
  failing reads in one `Ask`, a failure in one group after another group succeeded); a 33rd read
  started before a wait; a ticket, buffer, thread or descriptor reused before it is collected, or
  leaked on an error path;
- threads and Bend's runtime: a helper thread writing a heap block the main thread may free,
  move or reuse; allocation or garbage collection racing a helper; memory visibility (missing
  barriers or joins) between a helper's write and the main thread's read;
- the read-ahead queue: a piece lost, duplicated or reordered; an error or EOF reported for the
  wrong piece; the heap-full fallback; switching files (EBUSY) or piece sizes (EINVAL); a run
  that stops early (`-c e`, an error) with the helper blocked on a pipe, a FIFO or `/dev/stdin`,
  and whether the process still exits with the right code and output;
- BGZF behaviour unchanged from the reviewed driver (damaged, truncated or non-BGZF input);
- memory errors in the C code: bounds, `malloc` or `pthread_create` failure, integer overflow in
  sizes; where an out-of-memory failure now surfaces;
- a message lost, or a wrong exit code; the one-step build (`bend main.bend -o`) and `build.sh`
  behaving differently other than the stated "no BGZF in this build" error.

You may build and run it on small inputs (`./build.sh /tmp/fb_review`, then
`/tmp/fb_review norm -f test/edge/ref.fa test/edge/sorted.vcf`; `bgzip` and `samtools` are
installed), and you may write test files under `/tmp` only. Do not run anything on the
whole-genome files in `data/`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
