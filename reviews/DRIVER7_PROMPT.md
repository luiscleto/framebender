Review of framebender's trusted driver and build on the git branch `memory`, in
`/home/luisc/Work/bend-projects/framebender-mem` (read-only: do not modify, create or delete files
in the repository, and do not switch branches).

framebender's program is proven: `PROOF.bend` proves every law of `LAWS.bend` and `MACHINE.bend`.
What the proof does not cover is the trusted part: the driver, `main.bend` and `io64.c` (C
effects), the build, `build.sh`, and Bend's runtime itself. The comment above `law machine` in
`MACHINE.bend` lists exactly what the driver must do (read the files' bytes; hand each VCF piece
over as `E.enc` of its text; answer each reference read of an `Ask`, in order, with exactly
`truth(B.Fasta.parse(fasta), chrom, a, b)`; write exactly the bytes of each output buffer and
every message; report its own errors as one line on stderr with exit code 2), and that Bend's
runtime may stop a run with "bend: out of memory" (exit 1).

The previous driver was reviewed and accepted (`reviews/*-driver6.md`). This change cuts the
peak memory on the whole genome from about 550 MB to 345 MB, with identical outputs; the
measurements and the reasoning are in `notes/memory.md` (sections "Step 1" and "Implemented"; its
section "Open questions for the driver review" lists the author's own doubts: answer each).
`git diff main -- build.sh io64.c main.bend` shows the trusted part:
1. `build.sh` patches Bend 2.0.39's generated runtime between `bend -o` and the C compiler: in
   `heap_hand`, a freed block of a class whose keep limit is one block (256 KiB and up) goes to
   the shared bank at once instead of staying parked on the thread that freed it. Before
   patching, `build.sh` checks that the four places the patch relies on are exactly as expected,
   and stops otherwise. Check the patch against the runtime's allocator in the generated C
   (`heap_alloc`, `heap_alloc_miss`, `heap_free`, `heap_hand`, `bank_push`, `bank_pop`, `KEEP`;
   build one with `bend main.bend -o /tmp/<dir>/fb.c` to read it).
2. `io64.c`: reference reads go through 128 KiB parts on the reading thread's stack instead of a
   1 MiB `malloc`ed buffer.
The machine's own changes (reference windows of at most 4 MiB; the task runs on the piece
instead of a copy) are proven, and are not part of this review.

Look for, among others:
- the runtime patch: any path where the patched `heap_hand` pushes a chain of more than one
  block, a block twice, or a block still in use; races with other threads' `heap_alloc_miss`
  or `bank_pop`; the bank's capacity; whether the build-time checks refuse every runtime they
  were not written for (a changed `KEEP`, `KEEP_WORDS`, `NCLS`, `QUANTUM`, a GPU build, a second
  definition); `build.sh`'s failure modes (set -e, a failed `awk`, the temporary directory);
- the stack buffers: the stack available to a reading thread (default `pthread_create`
  attributes, `RLIMIT_STACK` unlimited or small), and on the calling thread when a thread cannot
  be created; a read that spans parts, a part that ends inside a line break, short reads, EINTR;
  bytes delivered to the wrong request or out of order; any error path changed;
- the one-step build (`bend main.bend -o`, without the patch) and `build.sh` giving the same
  output (the patch may change only memory);
- question 3 of the notes: with smaller windows, a damaged FASTA (one that breaks the `.fai`'s
  layout) is met at a different read, so the output written before the error differs in length
  (a prefix of the good output, the same error line and exit code). Acceptable under the
  comment on law machine?

You may build and run it on small inputs (`./build.sh /tmp/<dir>/fb`, then
`/tmp/<dir>/fb norm -f test/edge/ref.fa test/edge/sorted.vcf`; `bgzip` and `samtools` are
installed), and you may write test files under `/tmp` only. Do not run anything on the
whole-genome files in `data/`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
