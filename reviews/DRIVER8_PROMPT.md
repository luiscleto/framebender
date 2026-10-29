Review of framebender's trusted driver on the git branch `gz`, in
`/home/luisc/Work/bend-projects/framebender-gz` (read-only: do not modify, create or delete files
in the repository, and do not switch branches; the changes are uncommitted, so compare with
`git diff` and `git status`).

framebender's program is proven: `PROOF.bend` proves every law of `LAWS.bend` and `MACHINE.bend`.
What the proof does not cover is the trusted part: the driver, `main.bend` and `io64.c` (C
effects), the build, and Bend's runtime. The comment above `law machine` in `MACHINE.bend` lists
exactly what the driver must do, and now also how it writes the output bytes: to stdout or to
the `-o` file, plain or in BGZF (cut as bgzip 1.24 cuts, deflated by libdeflate at htslib's
level mapping, in order, the end-of-file block only when the exit code is 0, nothing after a
failed write), and its errors for the `-o` file.

The change adds compressed output, `-o FILE` and `-O v|z|z0..z9`. The law and the design passed
a three-model review (`reviews/*-compress-law.md`, decisions in
`reviews/responses-compress-law.md`); `notes/compress.md` has the design ("The driver") and what
was built ("Step 2", including "One buffer at a time", a change from the design, and the test
results). The previous driver was accepted (`reviews/*-driver7.md`). The trusted part to review:
1. `io64.c`, the output section (about 450 lines): the lazy open of the `-o` file and the
   identity check against the open inputs and stderr before `ftruncate`; the bgzip cut; the job
   ring, the N compressor threads and the writer thread; the bounded queue; the carried tail;
   the end-of-file block; error handling. Also the stream identities recorded in
   `Io.read_block`, and the runtime constructor's grammar for `-o`, `-O` and glued `-O…`
   (it must agree with `B.Args.parse` in `types.bend`, which is proven).
2. `main.bend`: `Io.out_set`, `Io.out_write`, `Io.out_close` in the loop, the reading of
   `B.Args.output` (a `None` after the start must be an internal error), the error messages.
3. `io64.js` (the JavaScript build's three effects; BGZF refused there).
4. `test/out.sh` and `test/gen_out.py`: do they test what the comment on law machine promises?

Look for, among others:
- any way the file decompresses to something other than the output bytes: blocks out of order,
  a block written twice or skipped, the carried tail lost or duplicated, a wrong CRC32 or ISIZE,
  a block over 64 KiB compressed (incompressible data), a short write counted as complete;
- any way a failed or stopped run leaves an end-of-file block, or a successful one lacks it;
  writes after a failed write; a driver error (`die`, exit 2) racing with the threads, or exit
  turning into a signal;
- data races, deadlocks or lost wake-ups in the ring and the queues (a slow or stalled reader,
  `--threads 1` and 128, an empty output, an output of exactly one block, a header longer than a
  block); memory not bounded as stated;
- the `-o` file: refusing an input by any name (symlink, hard link, `/dev/stdin`, `/proc/self/fd`),
  stderr redirected to the same file, a directory, a FIFO, `/dev/null`, `/dev/stdout`, no
  permission, an existing file left unchanged after every input error, `-o -`;
- the constructor's grammar disagreeing with `Args.parse` on any command line (the runtime's
  thread count and the output both depend on it);
- byte identity with `plain | bgzip -l L` at every level, and the level mapping.

You may build and run it on small inputs (`./build.sh /tmp/<dir>/fb`, then for example
`/tmp/<dir>/fb norm -Oz -o /tmp/<dir>/o.vcf.gz -f test/edge/ref.fa test/edge/sorted.vcf`;
`bgzip`, `tabix`, `bcftools` and `samtools` are installed), and you may write test files under
`/tmp` only. Do not run anything on the whole-genome files in `data/`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
