# Beating bcftools on the whole genome: plan (phase D, speed agent, 2026-10-28)

Brief: `notes/briefs/SPEED.md`. Build measured: `main` at c7f046d (phase C). No tracked file was
edited; every prototype is scratch C in `data/tmp/speed` (file list at the end).

**Status (2026-10-28):**
- Steps 1 and 2 (A1 + A2, then `.vcf.gz`) are written on branch `driver`, checked and timed:
  `notes/speed_driver.md`. Driver review 4 (`reviews/*-driver4.md`): GPT and Grok accepted;
  Claude's four findings (a `.vcf.gz` cut at a block boundary accepted; the CPU out-of-memory stop;
  the gzip wording; `$CC` in `build.sh`) are fixed and rechecked, see `notes/speed_driver.md`,
  "After driver review 4".
- Lead's decisions on section 4: (1) pinned timings, unpinned ranges beside them; (2) libdeflate
  through a two-step build (`build.sh`), BGZF only; (3) the `MACHINE.bend` trust comment goes to
  the driver review; (4) the boundary lemma stays inside the proofs; (5) write-behind dropped;
  (6) 400 MB batches are fine; (7) no upstream comments without the owner; (8) the README is the
  lead's.

## Summary

- **Profile (whole genome, to /dev/null, one sequential run of about 4.8-5.1 s):** the driver
  takes 1.6 s, of which 1.3 s is reading the FASTA (`Io.fa_read`); the machine takes the rest. Of
  the machine's ~3.9 s: per-record fast path 2.1 s, sorting buffer 0.8 s, zero-filling and growing
  the output buffer 0.5 s, copying records into it 0.5 s.
- **Writing to a file** costs 0.37 s in `write()` itself. The rest of the 1.5-2.5 s extra is the
  CPU running slower, not waiting: on this hybrid laptop CPU the main thread sometimes lands on an
  E-core, and kernel writeback (btrfs zstd compression and dm-crypt) competes for the cores while
  the run goes on. Pinned to the P-cores, the extra for a file is 0.4-0.6 s. The `cp` in the brief
  is a btrfs reflink (0.04 s, no data written); `cp --reflink=never` and `dd` take 0.6 s.
- **Driver only, measured** (pinned, to a file): a whole-line fast path in `Io.fa_read` plus reading
  the next VCF piece ahead in a helper thread: 5.34-5.53 s → 4.85-4.94 s. bcftools: 7.70-7.93 s.
  Writing behind in a helper thread gained nothing; drop it.
- **`.vcf.gz` through libdeflate, measured:** BGZF decompressed in the read-ahead thread: 4.86-4.92 s,
  against 7.90-7.96 s for `bcftools norm` on the same `.vcf.gz` and 6.17-6.20 s for today's
  `bgzip -dc | framebender`. libdeflate decompresses this file in 0.53 s on one thread.
- **Parallel machine:** 16-32 copies of today's binary on 1/N of the genome each finish in
  0.92-0.98 s together (4.35-4.50 s for one run on the whole file). A batched design inside the
  machine needs **no change to `protocol.bend` or `MACHINE.bend`**. A law about a parallel call
  (`pmap == map`) proves in a few lines and passes `--verdict`. Expected 1.0-1.8 s on the whole
  genome, 4-6x bcftools. Proof cost estimate 8,000-14,000 lines.
- **Order:** (1) the two driver changes, (2) `.vcf.gz` in the driver, which together give a 1.6x win
  with no proofs, (3) `lawful-halves` and the statement of the segment lemma, reviewed first,
  (4) the parallel machine, with parallel reference reads in the driver.

## 1. Profile

### How it was measured

- Machine: i9-13950HX, 8 P-cores (CPUs 0-15 with HT, up to 5.5 GHz) and 16 E-cores (16-31, up
  to 4.0 GHz); `powersave` governor; 30 GB RAM. `data/tmp` is btrfs with `compress=zstd:3` on
  dm-crypt; `vm.dirty_bytes` = 256 MB, `dirty_background_bytes` = 64 MB.
- Every run: `nice -n 19`, a timeout, `BEND_NO_TELEMETRY=1`, nothing else running (checked with
  `pgrep`), whole-genome inputs in the page cache, interleaved rounds.
- **Pinning.** Unpinned, framebender varies by up to 3 s between identical runs, even to
  /dev/null (HEAD: 5.07-7.87 s; `+RTS --threads 1` varies just as much, so it is not Bend's worker
  threads; the runtime sets no affinity). bcftools stays within 0.1 s. Pinned with
  `taskset -c 0-15` (P-cores), both tools vary by about ±0.15 s. The tables below are pinned unless
  marked; unpinned ranges are given where they matter.
- Driver time: wall-clock timers patched around each effect in the generated C (`fbt`). Machine
  split: a SIGPROF sampler (1 kHz, `-O3 -g -static`, 6,939 samples). Bend's loops compile to
  unnamed `spin_N` functions; they were matched to defs by their callers and bodies (e.g. spin_319
  is `BY.grow`).

### Where the time goes (HEAD, whole genome, 4,048,342 records, sequential)

| part | time | what |
|---|---|---|
| driver: VCF pieces (`Io.read_block`, 776 calls) | 0.27-0.33 s | `read` straight into the block |
| driver: FASTA windows (`Io.fa_read`, 175 calls) | 1.26-1.30 s | 2.9 G letters (chr1-22 once): 16 MiB bounce buffer, each line checked then `memcpy`'d, its LF taken one byte at a time; a 16M+64K-letter window needs a 32 MiB block, so about 15 MiB of padding is zeroed per read |
| driver: output (`Io.write_block`, 949 calls) | 0.001 s to /dev/null, 0.37 s to a file | |
| machine: fast path (cut, POS, alleles, INFO `END` scan, REF compare, pump) | ~2.1 s | `nat_mul` (POS parsed as a Nat) is 3% of all samples |
| machine: sorting buffer (`Ck` lists, the 16-field `Run` rebuilt per call, `flush.*`) | ~0.8 s | ~200 ns a record |
| machine: output buffer, allocation | ~0.5 s | each step: `take.len` allocates a new zero-filled block, then `reserve` grows it (`BY.grow`: another zero-filled block plus a copy of every word of the old one). Measured: skipping the zero-fill of big blocks saves 0.45 s |
| machine: output buffer, copying records (`F.append`) | ~0.5 s | |
| total (`rt`: user 4.3 s, sys 0.6 s) | 4.8-5.1 s wall | bcftools: 5.47-5.70 s |

The machine's split comes from sample shares (fast path 41%, sorting buffer 16%, output allocation
10%, output copy 10%, the rest kernel and driver), scaled to the measured machine time. Kernel time
is mostly the copies inside `read`/`pread`, so it is already counted in the driver rows.

### Why a file costs more than /dev/null

- The `write()` calls take 0.37 s (timers); `dd bs=4M` and `cp --reflink=never` of the input take
  0.59-0.63 s. On btrfs, plain `cp` is a reflink: 0.04-0.05 s, nothing written. So 0.3 s is not
  the cost of writing 2.8 GB; 0.4-0.6 s is.
- The rest is the CPU running slower: with a file, user time rises from 4.3 s to 5.2-6.2 s for
  the same instructions. Two causes:
  1. Core placement on the hybrid CPU (above).
  2. Writeback during the run: with `dirty_bytes` at 256 MB, writeback starts within the first
     second. Its zstd compression and dm-crypt run in kernel workers on other cores. A /dev/null run
     with an unrelated `dd` writing 2.8 GB alongside went from 5.4 to 8.1 s once.
- Pinned to the P-cores, the extra for a file is 0.4-0.6 s (HEAD: 4.79-5.10 s to /dev/null,
  5.34-5.53 s to a file), about the `write()` calls. Turning compression off for the output
  directory (`chattr +m`) changed nothing pinned (5.40-5.50 s).
- bcftools behaves differently: stable unpinned, but 2.2 s slower to a file even pinned
  (5.5 → 7.7 s). I did not investigate why.

## 2. Options

### A. Driver only (trusted code: a three-model driver review, no proofs)

Prototypes: `data/tmp/speed/tools/stage1.py` patches the generated C. Each prototype's stdout,
stderr and exit code are byte-identical to HEAD on the whole genome (`-c w`), chr22, `scr.vcf`,
`test/edge/*.vcf` and `data/tmp/edge2/*.vcf` (`-c e` and `-c w`).

**A1. A whole-line fast path in `Io.fa_read`.** Before today's per-run check: when the column is 0,
`lw = lb + 1`, `16 <= lb <= 64`, the whole line and its LF are in the buffer and fit `want`, test
the letters with 16-byte SSE2 compares (no LF, CR, space or tab) and the LF at column `lb`, then
store the 16-byte blocks. Anything else goes through today's code, so the rule and the codes 0/1/2
are unchanged. About 20 lines. SSE2 is baseline x86-64; keep the scalar path under
`#ifndef __SSE2__` for other targets.

FASTA microbenchmark (`fa/fabench.c`: chr1-22 in 16M-letter windows, one thread; every mode gives
the same letters, hash-checked):

| mode | time |
|---|---|
| today's algorithm | 0.92-0.98 s |
| today's + the whole-line path (A1) | 0.53 s |
| `pread` into the block, compacted in place | 0.47-0.51 s |
| from an `mmap` of the FASTA | 0.35-0.39 s |
| in place, 4 / 8 / 16 threads | 0.25 / 0.21 / 0.21 s |
| `mmap`, 4 / 8 / 16 threads | 0.15 / 0.14 / 0.13 s |

In the driver, A1 brings `Io.fa_read` from 1.26-1.30 s to 0.77-0.78 s. The rest is allocating
and padding the 32 MiB block; without the padding, 0.63 s. I recommend A1 rather than `mmap`
(SIGBUS if the file shrinks, a larger review) or reading in place (the block may be smaller than
the span on disk).

**A2. Read the next VCF piece ahead.** After a full piece, `Io.read_block` allocates the next block
(on the Bend thread) and a helper thread reads into it; the next call joins the helper and
returns that block. The errors and their messages are the same, at the same call. `read_block`
time on the critical path: 0.27-0.33 s → 0.024-0.030 s. For the review: a helper thread writes into
a heap block that no term references yet; every `heap_alloc`/`heap_free` stays on the Bend thread;
the runtime does not move blocks. At an early `Finish` (`-c e`) the helper may still be reading
when the process exits, which is harmless.

**A3. Write behind (measured, not recommended).** A helper thread writes the step's block; the
block is freed at the next write; messages wait for the write in flight, so stdout and stderr keep
their order; an exit handler reports a late error. A first version freed nothing and grew to
3.7 GB (fixed). Fixed, it gains nothing: 5.06-5.14 s against HEAD's 4.79-5.10 s to /dev/null;
with A1 and A2, 4.99-5.11 s against 4.85-4.94 s to a file. Writes are only 0.37 s, and freeing one
step later loses the heap's reuse of a warm block.

**Results** (whole genome, `-c w`, interleaved rounds, wall clock):

| build | /dev/null, pinned | file, pinned | file, unpinned (5 rounds) |
|---|---|---|---|
| HEAD | 4.79-5.10 s | 5.34-5.53 s | 6.76-7.80 s |
| A1 | 4.39-4.49 s | 4.90-5.02 s | |
| A2 | 4.67-4.75 s | | |
| A3 | 5.06-5.14 s | | |
| A1 + A2 | 4.35-4.50 s | 4.85-4.94 s | 5.33-6.22 s |
| A1 + A2 + A3 | 4.46-4.48 s | 4.99-5.11 s | |
| bcftools 1.24 | 5.47-5.70 s | 7.70-7.93 s | 7.75-7.84 s |

Uncompressed output directory, pinned: HEAD 5.40-5.50 s, A1 + A2 5.03-5.10 s, bcftools
7.40-7.61 s. chr22 and `scr.vcf` are unchanged (chr22 0.109-0.123 s for all three framebender
builds, bcftools 0.110-0.115 s; scr 0.122-0.131 s, bcftools 0.071-0.078 s).

**A4. Prefetching FASTA windows (not recommended).** Hiding the remaining 0.78 s would need
predictable windows: the machine asks `[POS-1-64K, POS-1+len+16M)`, which depends on the first
record the last window missed. With aligned windows (a small machine change), the driver could
read window k+1 while the machine works on k. The parallel design below does better: its reads are
batched and answered in parallel.

### B. `.vcf.gz` input through libdeflate in the driver

The GIAB `.vcf.gz` is BGZF (43,457 blocks) and decompresses byte for byte to `data/hg002.all.vcf`.

- libdeflate 1.26 (`gz/bgzf.c`, decompression and CRC32): 0.526 s on 1 thread, 0.271 s on 2,
  0.148 s on 4, 0.085 s on 8.
- Prototype (`tools/gz.py` on top of A1 + A2): `Io.read_block` checks the first 18 bytes for a BGZF
  header. If it finds one, the reads (the first piece, then the read-ahead thread's) go through a
  BGZF reader: block header, `libdeflate_deflate_decompress` straight into the piece when the block
  fits, else into a 64 KB carry buffer; CRC32 and ISIZE checked; a bad block fails the read.
  Output is identical to HEAD on the plain file past the header's command line, which names the
  `.gz`. Stderr is identical too.

Pinned, to a file, 3 interleaved rounds:

| run | time |
|---|---|
| framebender, BGZF in the driver (A1 + A2 + B) | 4.86-4.92 s |
| `bgzip -dc in.vcf.gz \| framebender ... /dev/stdin` (HEAD, the README's way) | 6.17-6.20 s |
| `bgzip -@4 -dc \| framebender` (A1 + A2) | 5.01-5.08 s |
| `bcftools norm` on the `.vcf.gz` | 7.90-7.96 s |
| `bcftools norm --threads 4` on the `.vcf.gz` | 7.60-7.64 s |
| for reference, plain VCF: A1 + A2 / bcftools | 4.74-4.87 s / 7.61-7.74 s |

Decompression in the read-ahead thread is fully hidden while the machine is sequential (it
consumes 0.65 GB/s; one libdeflate thread gives 5.4 GB/s on this file). For the parallel machine,
or VCFs that compress less, the read-ahead helper should decompress a piece's blocks on 2-4
threads.

What it changes and costs:
- Driver code: about 80 lines (the BGZF reader) and the parallel decompression later. Errors: a
  corrupt or truncated block should get its own message (e.g. `error: bad BGZF block in <path>`).
  Plain gzip that is not BGZF cannot be decompressed piece by piece with libdeflate: reject it
  with a message pointing to `bgzip`, or add zlib. That is a decision.
- **Linking:** `bend main.bend -o` runs `clang -std=c11 -O3 file.c -lpthread -lm` and adds only
  `-lX11 -ldl` / `-lasound` when those headers appear, so a C effect cannot ask for `-ldeflate`.
  Three ways: vendor libdeflate's decompressor (MIT, a few files) into the build; `dlopen`
  `libdeflate.so.0` when a `.gz` is opened; or an upstream ask for link flags on C effects. The
  timings above used `-ldeflate` directly.
- Trust boundary: the law's `vcf` becomes "the decompressed bytes" for a BGZF file. That is one
  more sentence in `MACHINE.bend`'s list of what the law does not cover (a comment, but in a
  contract file), in `docs/LAWS.md` and in the README, plus the driver review. libdeflate becomes
  trusted code.

### C. Sequential machine changes (proofs; no contract change)

Each is measured or estimated on its own. In the parallel design they run spread over all cores,
so they matter much less there; I would not do them first.

| change | gain | cost |
|---|---|---|
| C1. Output buffer: size the buffer `take` makes for the kept texts plus the next piece (no `reserve` grow), and `BY.grow` copying only the used words | up to 0.45 s (measured upper bound: no zero-fill of big blocks at all) | `norm_run` size and budget lemmas; `lawful-bytes` `grow` proof |
| C2. POS parsed on U32 (at most 9 digits) instead of Nat | ~0.15 s (`nat_mul` 3%) | `NF.num` lemmas (`proof_b_cut_num`) |
| C3. FASTA windows sized to fit 2^24 letters (lookahead 16M - 64K - len(REF)), so the block is 16 MiB with no padding | 0.05-0.1 s (measured: `fa_read` -0.15 s) | one constant in `fast.need`, budget lemma constants |
| C4. The sorting buffer (0.8 s) | | `Run` representation; the sort proofs. Not recommended |

An `Array.new` that does not zero-fill (bendlang/bend#1778, already open) would give C1's 0.45 s
with no change of ours; it would need `lawful-arrays` to model unspecified contents.

### D. The parallel machine

**Measured bound.** N concurrent runs of the A1 + A2 binary, each on 1/N of the genome (header
plus a slice cut at line boundaries), to /dev/null, wall clock for the group, 3 rounds:

| N, CPUs | time |
|---|---|
| 8 on the P-cores | 1.08-1.10 s |
| 16 on the P-cores | 1.00-1.01 s |
| 8 on all cores | 1.16-1.18 s |
| 16 on all cores | 0.93-0.95 s |
| 32 on all cores | 0.92-0.98 s |
| one run, whole file | 4.35-4.50 s |

This includes every run's own FASTA reads, sorting buffer and output copies. It flattens at about
0.93 s; memory bandwidth is the likely limit (the VCF read and copied, 2.9 GB of FASTA read and
compacted, the output buffers zero-filled).

**Design: batches inside the machine.** In body mode (header done, not halted, bytes mode), the
machine:

1. **Collects** up to K pieces (K = 32 at 3.5 MB) as sources without judging them: each `Chunk`
   answers `More`. The end of the file closes a batch early.
2. **Plans** (sequential, cheap): the line that straddles two pieces is joined as today
   (`pend ++` the head of the next piece); for each piece, the CHROM and POS of its first and last
   complete lines (two cuts).
3. **Asks once:** one `Ask` with one read per piece: its contig,
   `[firstPOS-1-64K, lastPOS-1+64K)` (capped at 2^31 letters). A piece whose first and last CHROM
   differ gets one read per contig, or is left to step 5's sequential path.
4. **Judges in parallel:** a fork-join (`lawful-halves`) over (piece, window) pairs. Each task runs
   **today's pump** on its own piece, from a speculative state S0: in body, `cur` the piece's first
   CHROM, empty buffer, zero counts, n = 0, no notes, the piece's window cached. A task stops as
   **dirty** at the first event it cannot handle alone: an `Ask` (a window miss, or a slow-path
   read), a note (any warning or stop), the String mode, a `Yield`. Otherwise it is **clean** and
   returns its final state T: its output bytes, its buffered items, its counts and line count, the
   CHROMs it saw in order, and the smallest key it wrote or buffered.
5. **Combines in order** (sequential): the straddling line first, with today's code. Then for piece
   i, if T_i is clean and `Pre(S, T_i)` holds, `S := shift(S, T_i)`, which costs about the buffer's
   length (~150 items). Otherwise piece i is rerun from the true state S with today's code, asking
   for reads as it goes. If S halts, the machine finishes and drops the rest of the batch.
6. **Hands out the output** one piece per step: each `Ask{[]}` gets another step, which
   `MACHINE.bend` allows explicitly. No concatenation copy.

`Pre(S, T)`: S is in body, not halted, in bytes mode; `S.cur` is T's first CHROM; none of T's later
CHROMs is `S.cur` or in `S.ended`; T's smallest key in its first CHROM run is at least S's
buffer's largest key and `S.last`'s key.

`shift(S, T)`: S's buffered items E all have keys at or below every item of T. So in the true run
they stay at the buffer's front, are written first, and a T item is never ready while an E item is
not (equal keys go after existing ones). The written text is S's, then the E items ready by T's
last input POS, then T's own output. The buffer is the rest of E followed by T's buffer. `last`,
counts and n add up. A CHROM change inside T writes the whole buffer, E included, at that point;
after it, T's state no longer depends on S except through `ended`.

**What changes in the contract: nothing is required.**
- `MACHINE.bend`'s law already quantifies over every cut `cs` of the VCF and says the program may
  "work on many lines in parallel".
- Pieces still arrive one per step.
- A batch's reads are one `Ask` with K requests: `protocol.bend` already allows "any number of
  reference reads, all answered at once".
- Output leaves over several steps through `Ask{[]}`.
- The step and read bounds (`bound`) allow K reads per K pieces with a wide margin.

Optional later, a contract change that needs the three-model review: a step's output as a list of
spans `(D.Bytes, s, n)` (`bytes_enc.bend`'s `E.out`, `MACHINE.bend`'s `absorb`, `norm.bend`'s
`Step`, the driver's write becoming `writev`). A clean piece's unchanged records could then be
written straight from its input block, with no copy and no output buffer to allocate. In the spike
that allocation was half of the parallel phase.

**What `lawful-halves` must state.** Only a parallel map; the combine is a sequential fold outside
it:
- a balanced tree built from a list, with `flatten(tree(xs)) == xs`;
- `pmap(f, t) == map(f, t)`, where `pmap` makes a parallel call `a b = pmap(f, l) pmap(f, r)` at
  each node;
- `flatten(map(f, t)) == List.map(f, flatten(t))`.

Checked: in `data/tmp/speed/halves_test.bend`, a `pmap` with a parallel call and its law
`pmap(t) == smap(t)` prove by plain induction. The checker reduces the parallel call to
`Node{pmap(l), pmap(r)}`. It passes `--check-only` and `--verdict` through `data/tmp/bcheck.sh`,
and the generated C forks. ARCHITECTURE's `pfold` for an associative `g` is not needed.

**Reference reads for many pieces.** One batched `Ask` per batch, one window per piece. Each task
owns its window block, so there is no shared block and no `Array.fork`. Adjacent windows overlap
only by their margins (2 x 64K letters per piece, about 3%). The total read is still about the
genome once. The driver should answer a batch's reads in parallel: a new effect taking the list of
spans, used by `answers`. With A1 that is ~0.15 s for the genome on 4 threads, against 0.53 s
sequential (`fabench`).

**The sorting buffer and `-c e` across pieces.**
- Sorted input (the common case): every boundary passes `Pre`, and `shift` carries the entering
  buffer.
- A record that sorts before the previous piece's buffered items (e.g. a rewritten record moved
  left across the boundary), a revisited CHROM, or an `UNSORTED` break: `Pre` fails or the task is
  dirty, and that piece runs sequentially from the true state. The result is exact, at the cost of
  one piece.
- `-c e`: a problem line is a note, so its piece is dirty. The sequential rerun stops with the
  exact message and line number, and the rest of the batch is dropped (at most one batch of reads
  wasted).
- `-c w`: warnings make their pieces dirty too, so a file with many warnings runs at today's speed.
  Later, tasks could carry notes with piece-relative line numbers that the combine shifts.
- The header and the first piece always run sequentially; batches start once the run is in body.

**Expected:** whole genome about 1.0-1.3 s to /dev/null. To a file, add one sequential writer
(0.4-0.6 s) unless the writes overlap the next batch: 1.4-1.8 s against bcftools' 7.7 s. chr22
(10 pieces, one batch) perhaps 0.05-0.08 s. Memory at K = 32: about 32 x (3.5 MB piece + ~4 MB
window + 4 MB output) ≈ 400 MB, against today's 130 MB.

**Proof work, estimated:**

| part | lines | notes |
|---|---|---|
| `lawful-halves` | 300-600 | its own law review (a non-bio package: the owner signs off) |
| segment lemma: `run.go(lines, RS) == shift(RS, run.go(lines, RS0))` under `Pre`, for lines whose run from RS0 never halts or writes a note | 2,000-4,000 | the main risk: `insert`/`take_ready`/`drop_ready`/`flush` with a sorted prefix of smaller keys in front. Builds on `proof_run_sort*` and phase B's run proofs |
| machine: collecting, the plan, the batched `Ask` (each piece's window truthful), the task as today's pump from S0 (S0 must satisfy the machine's invariant against RS0; to check: is phase B's invariant stated against any spec state, not only reachable ones?), `shift` on `NR.Run` (`ob` bytes, `front`/`back`), the fallback, the budget | 5,000-9,000 | reuses every per-line proof unchanged |
| driver: parallel answers to a batch, read-ahead of several pieces | | driver review |

Total 8,000-14,000 lines (phase C: 13,800; phase B: 57,000).

Risks:
- Bend's scheduler hands each task to one core and never moves it. Pieces are balanced by size,
  but E-cores are slower. The 32-run proxy suggests that is fine (0.92 s against 1.00 s on the
  P-cores alone).
- Each task zero-fills its own output buffer; in the spike that was half the parallel phase.
  Output spans or C1 fix it.
- Windows grow for pieces that span a gap in the calls (centromeres); still bounded by 2^31 per
  read.

## 3. Recommended order

1. **A1 + A2 in the driver.** Measured 5.34-5.53 s → 4.85-4.94 s to a file, pinned; bcftools
   7.70-7.93 s. Unpinned 5.33-6.22 s, against 7.75-7.84 s. No proofs; `test/same.sh`,
   `test/compare.sh` on the whole genome, and the three-model driver review. A few hours.
2. **`.vcf.gz` through libdeflate (B)**, in the read-ahead thread. Measured 4.86-4.92 s against
   bcftools' 7.90-7.96 s on the same `.vcf.gz`. Driver review and the trust-boundary sentence.
   With step 1, a clear, reproducible 1.6x win on real inputs, with the laws and proofs untouched.
3. **De-risk the parallel machine:** write and prove `lawful-halves` (small), and write the
   segment lemma's statement and `Pre`/`shift` for review before any machine code.
4. **The parallel machine (D)** and parallel reference reads in the driver. Expected 1.0-1.8 s,
   4-6x bcftools. The big proof.
5. Later, only if needed: output spans (a contract change), C1-C3.

## 4. For the lead to decide or ask the owner

1. **Benchmark protocol:** report pinned runs (`taskset -c 0-15`, both tools) as the reproducible
   comparison, with unpinned ranges beside them. Unpinned framebender runs vary by up to 3 s on
   this hybrid CPU.
2. **Linking libdeflate:** vendor it, `dlopen` it, or ask Bend upstream for link flags on C
   effects. And plain (non-BGZF) gzip: reject it with a clear message, or add zlib?
3. **The `.vcf.gz` trust boundary:** the sentence in `MACHINE.bend` (a contract file, comment
   only), `docs/LAWS.md` and the README. Does it need the three-model contract review, or the
   driver review only?
4. **The segment lemma:** a proof-internal lemma (my proposal: the machine law already covers the
   result), or the reviewed law ARCHITECTURE planned ("the run on a whole file equals the runs on
   its pieces, joined")?
5. **Write-behind (A3):** measured with no gain; I propose dropping it.
6. **Parallel batch parameters:** K = 32 pieces of 3.5 MB (~400 MB of memory), or smaller.
7. **Upstream:** add the measured 0.45 s to bendlang/bend#1778 (an `Array.new` without zero-fill);
   ask for link flags on C effects if libdeflate is not vendored.
8. The README's speed table is out of date (8.5 s against 9.1-9.7 s); update it after step 1, with
   pinned numbers.

## Scratch files (`data/tmp/speed`, ignored; whole-genome outputs and slices deleted)

| file | what |
|---|---|
| `fb.c`, `fb_head` | HEAD's generated C and binary (`clang -std=c11 -O3 fb.c -lpthread -lm` is what `bend -o` runs) |
| `tools/patch.py` → `fb_t` | wall-clock timers around each effect (`FBT=1` prints them) |
| `tools/prof.c`, `tools/sym.py`, `fb_ps` | SIGPROF sampler (`PROF_OUT=file`) and symbol histogram |
| `tools/rt.c` | wall, user, sys, max RSS, faults of a command (no `/usr/bin/time` here) |
| `tools/stage1.py` → `fb_s1{a,b,c,ab,abc}` | driver prototypes A1, A2, A3 |
| `tools/gz.py` → `fb_s1abz` | BGZF input through libdeflate (`-ldeflate`) |
| `s1t_abnz.c`, `s1t_abnp.c` | `NOZERO=1`: no zero-fill of big `Array.new` blocks; `NOPAD=1`: no FASTA block padding (timing only) |
| `fa/fabench.c`, `fa/fabench_sum.c` | FASTA window microbenchmark (modes 0-3, threads; `_sum` hashes the letters) |
| `gz/bgzf.c`, `gz/bgzf_nh.c` | libdeflate BGZF throughput (with / without a byte hash) |
| `bench1.sh`, `bench2.sh`, `bench3.sh` | interleaved whole-genome runs; `.vcf.gz` runs; N concurrent runs on slices (`tools/slice.py` makes them) |
| `halves_test.bend` | the parallel call under a proven law |
