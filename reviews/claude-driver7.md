# Driver review 7 (branch `memory`): runtime heap patch and stack read buffers

## Context
I reviewed the trusted part of the `memory` branch: the heap patch in `build.sh` and the 128 KiB
stack buffers in `io64.c`. I read it against Bend 2.0.39's allocator in an existing generated
runtime (`data/tmp/mem/fb.c`; the runtime part is the same for any program). Plan mode was on, so I
built and ran nothing. The checks to run are listed at the end.

## Verdict: ACCEPT once item 1 is fixed (2 and 3 are minor)

1. **should fix**: `io64.c:533` `char buf[IO64_PART]`, with threads made at `io64.c:663`
   `pthread_create(&s->th, NULL, ...)`. A thread made with default attributes gets a stack as
   large as the soft `RLIMIT_STACK` (2 MiB when unlimited, 16 KiB at least). glibc puts one 4 KiB
   guard page below it, and clang 23 does not probe large stack frames by default (no
   `-fstack-clash-protection`). Trigger: `ulimit -s 64; fb norm -f ref.fa x.vcf`. The 128 KiB
   frame then starts about 64 KiB below the thread's stack, past the guard page, and `pread`
   writes there: into another helper's stack or buffer (wrong letters with exit 0), or it fails
   with EFAULT ("cannot read"). With `ulimit -s 128` it lands in the guard page: EFAULT. The old
   `malloc` buffer had no such failure. With today's 8–16 MiB the margin is large, so this only
   bites at unusual limits. But here the failure is silent, and the law needs a clean error.
   Fix: give each slot its own buffer instead of using the stack:
   `static char io64_fa_buf[IO64_FA_MAX][IO64_PART];` (in `.bss`; only touched pages stay
   resident, about the same as the stack pages glibc caches today), passed as `io64_fa_do(r,
   buf)`. A slot belongs to one read until `fa_wait` joins it, so no two reads share a buffer, and
   this also covers the case where the read runs on the calling thread. Another fix is a
   `pthread_attr_setstacksize` of `IO64_PART` plus 256 KiB, but that leaves the main-thread
   fallback depending on `RLIMIT_STACK`.

2. **minor**: the build-time checks in `build.sh`. Two cases pass them:
   - a second definition of `heap_hand` spelled differently (`INLINE …`, or under `#if`), which
     the awk range never sees;
   - a second call of `heap_hand`, for example a flush of every class. The patched code pushes
     `ALC_AT` without the unpatched `if (cold)` test, so it can push a head of 0. That is harmless
     today: `bank_pop` reads it as "empty" and takes a fresh quantum.

   Fix: also require `[ "$(grep -c 'heap_hand(' "$c")" = 2 ]` (the definition and the call in
   `heap_free`). The comment's claim of 256 KiB and up also depends on two unchecked lines,
   `KEEP_WORDS = gpu ? CHUNK : CAP_WORDS;` and `#define CAP_WORDS 32768`. Pin those as well, or
   drop the size from the comment. Safety does not depend on them (see Q1).

3. **minor**: stale comments. `io64.c:17` ("A read buffer … fails with ENOMEM"), `main.bend:25`
   ("no room for a read's buffer") and the comment on law machine at `MACHINE.bend:192` ("a read's
   buffer") still list a `malloc`ed read buffer. None is left: a reference read no longer
   allocates. On a CPU build, "out of memory" now comes only from libdeflate's decompressor (or a
   rare ENOMEM from `read`/`pread`). Fix the wording. Only comments change, so no proof is
   affected.

## Answers to the notes' open questions
- **Q1, the patch.** The argument holds:
  - `KEEP_WORDS` is 2^15 on the CPU (`corpus_setup`), so `KEEP(cls) == 1` exactly when cls ≥ 15.
  - `NCLS` is 8, so a fresh quantum for those classes is one block, with link 0.
  - A miss sets `ALC_AT = H[got] = 0` and `LEN = 0`. Each free then gives `LEN = 2^cls ≥
    KEEP_WORDS`, so `heap_hand` runs at once.
  - So the chain pushed is always exactly the block just freed, with link 0. It is pushed once,
    by its owner, and the unpatched code would have banked the same block one free later.

  The bank's capacity, `2·(cap >> (c−7))`, is at least the number of class-c blocks that exist.
  `bank_push` and `bank_pop` take the same `bank_lock` as `corpus_grow`'s relocation. The
  release and acquire on that lock order the link write before another thread's `H[got]` read in
  `heap_alloc_miss`. The patch is also memory-safe for any `KEEP_WORDS`/`NCLS`/`QUANTUM`: it banks
  the whole null-terminated chain, as the unpatched cold path does, and the miss follows links.
  Other values only skew the `LEN` bookkeeping, which the unpatched code would skew the same way.
  On a GPU build the device never calls `heap_hand` (the pinned `!DEVICE` guard), and `build.sh`
  never builds one. The checks refuse the five cases the notes tested; item 2 lists the two gaps.
- **Q2, the stack.** Normally there is enough margin (≥ 2 MiB against about 129 KiB). It is not
  enough under a small `ulimit -s`: item 1.
- **Q3, smaller windows.** Acceptable. The law covers only P.Fasta.plain files with truthful
  reads. A layout failure is one of the driver's own exit-2 errors, and nothing promises how much
  stdout comes before such an error. That length already depends on `--threads` and the reads in
  flight. The answers before the failing read are truthful, so stdout is still a prefix of what
  run writes. Optional: say this in the comment on law machine.

## Checked, no finding
- **Reading.** Parts now cut a span (up to 4 MiB) into about 32 pieces. The state carried across
  parts is unchanged (col, n, code, done): a CR at the end of one part and its LF in the next is
  handled, the fast line path needs a whole line inside the part, and `pread` retries short reads
  and EINTR. The error paths are the same minus the old ENOMEM. Each request's bytes go to its
  own block, and answers come in ticket order.
- **`build.sh`.** `set -e` stops on a failed `mktemp`, `bend`, `awk` or `clang`. The `one`
  checks run as `if` conditions, where a missing match gives "0" and refuses. The temporary
  directory is removed by the trap.
- **One-step build against `build.sh`.** The patch changes only which free block is reused. Every
  driver block is padded (`io64_pad`), and the runtime already reuses freed memory on one thread
  (`--threads 1`), so nothing can depend on fresh memory being zero. Outputs should match. Only
  the point where the heap runs out moves, which the law allows ("bend: out of memory").

## Checks to run (not run: plan mode)
1. `./build.sh /tmp/fbr/fb` and `bend main.bend -o /tmp/fbr/fb1`. On every `test/edge` input and
   with `--threads 1/4/32`, `cmp` both programs' stdout, stderr and exit codes.
2. `(ulimit -s 64; /tmp/fbr/fb norm -f test/edge/ref.fa test/edge/sorted.vcf)` before and after
   fix 1.
3. A fake `bend` that adds an `INLINE void heap_hand(...)` under `#if 0`: `build.sh` must refuse
   it after fix 2.
