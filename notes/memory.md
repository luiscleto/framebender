# Memory (phase F): where it goes, and the options

Brief: `notes/briefs/MEMORY.md`. Branch `memory`, on 09fabba. Steps 1 and 2 only; nothing
implemented outside `data/tmp/mem/` (scratch), nothing committed.

All runs: whole genome (`data/hg002.all.vcf`, `-c w`, to a file deleted before each run), pinned
`taskset -c 0-15`, `nice -n 19`, under `flock data/tmp/bench.lock`, interleaved, peak RSS from
`getrusage(RUSAGE_CHILDREN)`. Every build below wrote the same output (xxh64 `3469a25b962abb21`;
`.vcf.gz`: `375d7dbba07de9bf`) and passed chr22 byte for byte.

## Step 1: where it goes

**Method.** `data/tmp/mem/patch_mem.py` instruments a copy of the generated C (`bend main.bend -o`):
fresh heap words per block class (the bump allocator), live blocks per class (per-thread
counters, summed every 5 ms), every block of 8 KiB or more by call site (return address,
`addr2line` on a `-g -no-pie` build), RSS and the heap's bump pointer every 5 ms, and
`/proc/self/smaps` at the peak. It costs about 0.03 s, and 68 MB of its own tables (subtracted
below).

**How Bend's heap behaves** (the runtime's C, `heap_alloc`, `heap_free`, `heap_hand`, `bank_*`):
- A block of class c is 2^c words (a packed buffer of 2^d bytes is class d - 1). Memory is taken
  from an 8 GiB mapping by a bump pointer and never given back; a freed block can only be reused
  by the same class. So the heap's peak is the sum over classes of each class's own peak, not
  the peak of the sum.
- Each thread keeps freed blocks per class. For blocks of 256 KiB and more, a free parks the
  block as that thread's one "cold" block and moves the previous cold one to the shared bank.
  So a block freed on a worker thread stays parked there until that worker frees another block
  of the same class, while the main thread, which allocates every piece and window, misses it and
  takes fresh memory. Up to one block per worker per class is stranded this way.

**The current build at its peak** (instrumented 694 MB − 68 MB of instrumentation = 626 MB;
uninstrumented runs measure 557-600 MB here and 600-670 MB in the lead's runs, since the window
classes depend on thread timing):

| what | MB |
|---|---|
| **Bend heap** (bump pointer) | **559** |
| 4 MiB blocks: 81 at once (exact maxima by call site below) | 324 |
| — VCF pieces: 16 in the batch + 16 in the driver's read-ahead ring (`io64_ahead_give`) | 128 |
| — the task's copy of its piece (`task.of` → `NR.put_bytes`) | 64 |
| — the task's output buffer (`NR.reserve` in `task.run0`) | 64 |
| — FASTA windows of up to 4 Mi letters (`io_fa_start_run`), up to 17 | 68 |
| 8, 16 and 32 MiB windows (classes committed: 80 + 32 + 96) | 208 |
| — of which stranded on worker threads (committed minus max live: 16 + 0 + 64) | 80 |
| 2 MiB and smaller big blocks; small objects | 27 |
| **Outside the heap** | **~67** |
| malloc arenas holding the 1 MiB FASTA bounce buffers (one arena per helper thread, ~32) | ~47 |
| the runtime's fixed regions (rings, stacks, banks), the binary, libc, thread stacks | ~20 |

Where the big windows come from (all 794 reads logged): 639 fit 4 MiB (604 of them need all
of it), 141 take 8 MiB
(a piece of 3.5 MB spans about 3.9 Mb of genome; with 2 × 64 Ki of margin many go just past
4 Mi letters), 6 take 16 MiB and 8 take 32 MiB: 3 pieces spanning 20-28 Mb (gaps), and 5 reads
of exactly `ahead()` + `margin()` letters (Q's own reads, and the two-contig plan), which is
16 Mi + 64 Ki and so needs a 32 MiB block.

**Why one piece per batch on one thread still cost ~300 MB more than the sequential machine:**
the ring of 16 pieces (64 MB), the 32 MiB windows from `ahead()` (one live, but several
committed), and stranding. **The sequential machine with today's driver** measures 180-183 MB
(141 MB with the old one-piece read-ahead): 17 pieces (68 MB) and two of Q's 32 MiB windows
(64 MB) during a window switch.

## Step 2: options

Each measured as a scratch build (`data/tmp/mem/var.py` patches the generated C; the machine
prototypes are edited copies of the tree in `data/tmp/mem/t_*`). Rounds: 3 (2 for `.vcf.gz`).
"cur" is today's build, measured in the same sessions: 1.84-1.86 s, 557-596 MB.

### Free (no time cost), in the recommended order

| # | option | where | time | peak RSS | saving |
|---|---|---|---|---|---|
| 1 | big blocks freed straight to the shared bank (no stranding) | runtime, patched by `build.sh` | 1.80-1.82 s | 505-507 MB | ~85 MB |
| 2 | FASTA bounce buffer 128 KiB on the helper's stack (was 1 MiB `malloc`) | `io64.c` | 1.77 s | with 1: 489-492 MB | ~15-30 MB |
| 3 | no window over 4 MiB: task windows capped, Q's `ahead()` shortened to fit | `norm.bend`, `norm_seq.bend` | with 1+2: 1.78-1.82 s | with 1+2: 390-400 MB | ~90 MB |
| 4 | no copy of the piece | `norm.bend` (+ proofs) | with 1+2: **1.57-1.63 s** | with 1+2: 421-430 MB | ~60 MB, and 0.2 s faster |
| | 1+2+3+4 (4 as a partial prototype, see below) | | **1.67-1.69 s** | **358-361 MB** | |

1. **Stranding** (`strand` in `var.py`): in `heap_hand`, a class whose keep limit is one block
   (256 KiB and up) pushes the freed block to the bank at once instead of parking it. After it
   every class's committed memory equals its maximum live (measured). A three-line patch to the
   runtime's C, which `build.sh` would apply to the generated file (a `sed` or a small script);
   it is outside our proofs either way (the runtime is trusted), so it needs the three-model
   driver review, and is worth reporting to Bend upstream. Bend's own options cannot do it: the
   runtime has only `--threads` and `--gpu`, and no setting for its heap.
2. **Bounce buffers** (`part=131072`): `io64_fa_do` reads in parts of 128 KiB on its own stack
   instead of a 1 MiB `malloc`, which glibc serves from a per-thread arena and keeps. 8 times as
   many `pread`s; no measurable cost. Driver only.
3. **Windows of at most 4 MiB** (`t_cap_a`): `plan.reqs` asks one window when the span fits
   4 Mi letters (as now); two halves overlapping by 2 × `margin()` when it fits two; else the
   first and last 4 Mi letters (a record in between makes the task dirty and the piece goes to
   Q: a few pieces of 772, a few ms each). And `ahead()` = 4,128,760 so Q's reads (`ahead()` +
   `margin()`) fit 4 MiB. Then every big block is one class and they all share one pool.
   - The task windows alone save only 20 MB (463-468 MB): Q's 32 MiB reads still commit their
     class. Both together: 390-400 MB.
   - The smaller `ahead()` also brings **the sequential machine from 180-183 MB to 101-103 MB**,
     4.99-5.05 s against 4.92-4.94 s (within noise; `--threads 1` would gain it).
   - Proofs: `plan.reqs` is used in one place, `proof_e_task_buf.bend` (`reqs.if`, `reqs_ok`,
     `lrs`: two reads, each within 2^31 letters, of bytes contigs; about 80 lines to redo, with
     every new read built by `plan.win` so `win_ok` gives its bound). `ahead()` appears in the
     phase-B proofs only as `Norm.ahead()`, so those should only need re-checking. Then the
     full gate.
4. **No copy** (`t_nocopy`): the task keeps no copy of its piece. Measured with a prototype
   that copies only the bytes up to the piece's first LF, which is all the combine reads for a
   clean task (`feed_line` handles the line across the boundary, then the splice drops it).
   It is correct only when no piece goes dirty (true on the whole genome), so it is not a design;
   it measures the saving: 60 MB **and 0.2 s** (the copy runs inside each task, on the critical
   path). On top of 3 (where a few pieces do go dirty) the prototype keeps the full copy for the
   ~150 pieces with two windows, so 358-361 MB understates the saving; a full version should
   land near 330 MB.
   - The real change: a dirty task must hand back its piece intact. Q drops its input buffer
     when it reaches the last partial line, so the task must stop before that and take the piece
     back from Q's input (notes/parallel.md, open point 2). Proofs: a new invariant that the
     piece is in Q's input, unchanged, at every early exit of the task loop (area D:
     `proof_e_task_loop`, `_run`, `_piece`, `_one`), and the combine's use of `TOut.b`
     (`proof_e_wrap_comb`, `_clean`). The largest of the four; I would put it at the size of
     one phase-E area.

### Trade-offs (cost time against today's machine with 1-4)

| option | where | time | peak RSS |
|---|---|---|---|
| read-ahead ring of 8 pieces (was 16) | `io64.c` | +0.06-0.1 s (+4-6%) | −30 MB |
| ring of 4 | `io64.c` | +0.1 s (+6%) | −50 MB |
| pieces of 1.6 MiB (was 3.5) and windows capped at 2 MiB | `main.bend` (+ 3's constants) | +0.1-0.15 s (+6-9%) | −150 to −175 MB |
| `kmax` 8 (was 16) | `norm.bend` (`kmax` is abstract in the proofs) | +0.25 s (+14%) | about −105 MB |
| pieces of 3 MiB | `main.bend` | +0.1 s | −12 MB: not worth it |
| `kmax` 32 | | same | +170 MB |
| pieces of 1.6 MiB with `kmax` 32 | | slower than with `kmax` 16 | +65 MB over `kmax` 16: not worth it |

Measured combinations:

| build | time | peak RSS |
|---|---|---|
| 1+2+3, pieces 1.6 MiB, cap 2 MiB, `ahead()` to fit 2 MiB | 1.90-1.94 s | 216-222 MB |
| 1+2+3+4 (partial), same | 1.78-1.85 s | 207-213 MB |
| 1+2+3+4 (partial), ring 8 | 1.78-1.80 s | 327-333 MB |
| same on `.vcf.gz`: cur / 1+2 / 1+2+3 / 1+2+3+4 / + 1.6 MiB pieces | 1.87-1.88 / 1.79-1.84 / 1.83 / 1.67-1.69 / 1.78-1.80 s | 583 / 478 / 390 / 359 / 207 MB |

So with 1-4, pieces of 1.6 MiB give about 210 MB at today's speed (1.8 s), or keep 3.5 MiB
pieces for about 330-360 MB at 1.6-1.7 s. That makes the piece size the natural knob for a
memory/speed trade (a `--threads`-style option could set it, together with `kmax`).

**What remains after 1-4** (3.5 MiB pieces, from the instrumented 1+2+3 build, 383 MB heap): 4 MiB
blocks are 93% of the heap, 89 at once: 32 VCF pieces (batch + ring), up to 25 windows (pieces
split in two hold both halves), 16 copies (gone with 4), 16 output buffers; plus ~27 MB of
smaller blocks and ~20 MB outside the heap. Roughly 4 MiB × (ring + 3.5 × kmax) + 50 MB. Getting
near the sequential machine's ~100 MB means fewer bytes in flight: smaller pieces, fewer of them,
or a shorter ring.

## Recommended order

1. Stranding fix (`build.sh`) and 128 KiB bounce buffers (`io64.c`): driver only, one driver
   review, −100 MB, no time.
2. Windows of at most 4 MiB and the shorter `ahead()`: −90 MB, no time, sequential machine
   −80 MB; about 80 lines of proof in one file and the gate.
3. No copy: −60 MB and −0.2 s; the biggest proof job.
4. Then the owner's call on the trade: 1.6 MiB pieces (about 210 MB at today's speed once 1-3
   are in) or a ring of 8 (−30 MB, +5%).

## Implemented (2026-10-29): options 1, 2, 3 and the real no-copy

The lead's decisions: implement 1, 2, 3 and 4 (with its proofs) in that order; keep 3.5 MiB
pieces as the default; keep the diffs local (branch `threads` changes norm.bend's state, about
60 sites in 9 `proof_e_*` files, types.bend, MACHINE.bend, main.bend, io64.c and build.sh).

### 1. The runtime patch (`build.sh`)

`build.sh` patches the generated C between `bend -o` and clang: `heap_hand` gets, as its first
statement,

    if (KEEP(cls) == 1) {
      bank_push(e.mem, cls, ALC_AT(e, cls));
      ALC_AT(e, cls) = ALC_LEN(e, cls) = 0;
      return;
    }

so a freed block of a class whose keep limit is one block (256 KiB and up on the CPU) goes to the
shared bank at once instead of becoming the freeing thread's parked ("cold") block. Before
patching, `build.sh` checks that the generated runtime is exactly the one this was written for
(Bend 2.0.39): the whole of `heap_hand` (8 lines), the `KEEP` macro, the line of
`heap_alloc_miss` that takes `KEEP(cls)` blocks from the bank, and the line of `heap_free` that
calls `heap_hand`, each found exactly once. Otherwise it stops with "build.sh: the generated
runtime is not the one the heap patch was written for (Bend 2.0.39); see notes/memory.md" and
exit code 1. Tested with a fake `bend` that alters each of the four places, or adds a second
`heap_hand`: all five builds stop with the message.

Why it is safe: for such a class the thread's chain is empty except at the moment of a free
(each miss takes a one-block generation, whose link is 0, and a free hands its chain at once), so
the chain pushed is exactly the freed block, a one-block generation, which is what `heap_hand`
would have pushed one free later. `bank_push` takes the bank lock. Smaller classes are unchanged.

### 2. Reference-read buffers (`io64.c`)

`io64_fa_do` reads in parts of 128 KiB (`IO64_PART`, was 1 MiB) through a buffer on the reading
thread's stack (was `malloc`, which a per-thread glibc arena kept); comments updated. A read can
no longer fail for want of a buffer.

### 3. Windows of at most 4 MiB (`norm_seq.bend`, `norm.bend`)

- `ahead()` is 4,128,767 (was 16,777,216): a read of `ahead() + margin() + 1` letters fits a
  4 MiB block. Q's reads were 16 Mi + 64 Ki letters, in 32 MiB blocks.
- `plan.reqs` asks one window only when the span also satisfies
  `Nat.is_le(Nat.sub(Nat.sub(e, a), Q.margin()), Q.ahead())`, else the existing pair of reads
  (`ahead()` on from the first line, `ahead()` back from the last; a record between them that
  neither covers makes the task dirty). Written that way because the checker expands the closed
  `Nat.add(Q.ahead(), Q.margin())` until its stack overflows.
- Proof: `proof_e_task_buf.bend` (`reqs.if`, `reqs_ok`: the condition gained a conjunct; 3 lines).
  `ahead()` appears in phase B's proofs only as `Norm.ahead()`: they check unchanged.

### 4. No copy of the piece (`norm.bend` and proofs)

**The code.** A task runs Q on its piece itself and hands it back with its result
(`TOut{piece, result}`), so the combine (the line across the boundary, a merge that fails, a
dirty piece) has it as before. Q keeps the piece as its input until it reaches the piece's last
partial line, where it would move that line to `pend` and drop the buffer. So, before each
advance, the task tests (`swap`): if the piece's byte `el` is an LF with `at <= el < len` (`el`:
the piece's last LF, found once by `rlf`, the plan's backward search; only a hint, the test reads
the byte), Q keeps the piece; else Q's input becomes a copy of the bytes from `at` (at most the
last partial line, `put_bytes` into a block of their size) and the task holds the piece (`Ph`:
`PIn` or `PHeld`). Every exit (window miss with no spare window, a stop, Yield, Idle, fuel)
takes the piece back from the task or from Q's input (`task.back`). Q in the String mode makes
the task dirty at once (`task.next`; before, the task went on in that mode to the same dirty
end). New code: about 120 lines in norm.bend's task section (`Ph`, `src_b`, `st_b`, `task.back`,
`task.dirty`, `swap.*`, `swap`, `task.tgo`, `task.next`, `task.idle`, `task.last*`), and
`task.copy` is gone.

**The proofs.** The loop's proof must know that every advance keeps Q's input buffer. That is
new in phase B's simulation:
- `proof_b_simdefs.bend`: `S.Kept(p, p2)`, the last component of all five `AdvG` cases: from the
  byte mode, unless the first source's text holds no LF, that source is the same buffer (from
  some `at2` on) before the same later sources. Producers: `went_line` (every line path: the
  buffer from `lf + 1`), the two end-of-buffer cases (`part.len`: refuted by their own `nolf`
  fact), the two byte-mode Wants, `to_ms`, Ended and Yield (`kept_same`), Idle (no source), the
  String mode (`Unit`). Consumers that take the tuple apart: `proof_e_wrap_qx`, `_fb`, `_clean`
  (one more split). Files: `proof_b_simdefs`, `proof_b_adv_wf` (`kept_same`, `kept_md`),
  `proof_b_adv`, `_tostr`, `_line`, `_part`, `_msx`, `_slow`, `_fast`.
- `proof_e_task_tail.bend` (new, 178 lines): `nolf_at` (the piece's byte `el` is an LF,
  `at <= el < len`: its text from `at` holds an LF, from lawful-bytes' `at_view_t`), `tail_put`
  (the copy of the bytes from `at`, bounds discharged) and `tail_text` (it has the piece's text
  from `at`).
- `proof_e_task_loop.bend`: the loop's pictures gain where the piece is (`PhP`, `Hold`, `Hold0`);
  `LoopG` is now about `TOut{piece, result}`; new `kept_in`/`kept_hold` (S.Kept keeps the piece),
  `inv_sw` (a state whose source is replaced by one with the same text keeps the invariant),
  `tail_k`/`tail_ok`/`if_ok`/`lt_ok`/`next_in`/`next_ok` (the swap test's cases), `want_go`,
  `idle_go`, `step`, `loop_ok`, `start_ok`.
- `proof_e_task_one.bend`: one task: `rlf` hands the piece back (`BUF.rlf_b`), then
  `LP.start_ok`; the copy lemmas are gone (`TOutOK`'s statement is unchanged: the buffer handed
  back is the piece itself).
- Size: about 800 lines added and 230 removed in 18 files, plus the new file.

### The gate and the checks

All through `test/bcheck.sh`, on the final tree:
- `PROOF.bend --check-only` ALL PROOFS CHECK; `--verdict` ALL PROOFS CHECK (55 s);
  `examples.bend` 15 TODOs, `MACHINE.bend` 15 TODOs, `main.bend` 75 defs rely on unsafe or
  foreign code (all as before).

Against the base build (09fabba's `main.bend`, built the same way), with the final build at
piece sizes 3,670,016, 70,001, 1,000 and 300 (each from `build.sh`, the size replaced in the
generated C):
- `test/same.sh` 128/128 and `test/par.sh` 312/312 at all four sizes (also after options 1-3
  alone, and after the first no-copy code);
- gz suite 252/252 at all four sizes; end-of-file suite as expected at three sizes, and at 300 the
  same 8 lines as the base build at 300 (`edge_in`, `edge_in2` under `-c e`, known);
- pipe and FIFO: chr22, scr and `snp_sorted` under `-c w`/`-c e` at 3,670,016, 1,000 and 300
  (12 comparisons each), and the whole genome plain and `.vcf.gz` through both: identical;
- whole genome, `-c w` and `-c e`, plain and `.vcf.gz` (same relative paths): stdout, stderr and
  exit code identical;
- `test/compare.sh` (bcftools 1.24): chr22 0, scr 0, `test/edge/sorted.vcf` 1 (the `<DEL>`
  record), whole genome 0, whole genome from `.vcf.gz` 0;
- damaged FASTAs (chr22 with a space or a CR in place of a letter, cut short, both) at
  3,670,016, 70,001 and 1,000, `-c w`/`-c e`: the same error line and exit code as the base build,
  and both stdouts are prefixes of the good output; **the stdouts differ in length** (20 of 24):
  the reads now cover smaller windows, so the read that meets the damaged byte comes at a
  different point (mostly later). A damaged FASTA is outside the law (the FASTA premise).
  (Scripts: copies of `same.sh`, `par.sh`, `gztest.sh`, `eoftest.sh`, `fifotest.sh` writing
  to `data/tmp/mem`, so the threads agent's runs are not disturbed.)

### Measured (whole genome, `-c w`, interleaved, under the lock)

| run | base (09fabba) | final | |
|---|---|---|---|
| plain, file, pinned, 5 rounds | 1.86-2.01 s, 594-604 MB | 1.74-1.93 s, 344-345 MB | |
| `.vcf.gz`, file, pinned, 5 rounds | 1.90-2.17 s, 596-605 MB | 1.80-2.10 s, 344-348 MB | |
| plain, /dev/null, pinned, 3 rounds | 1.38-1.50 s, 586-600 MB | 1.27-1.30 s, 344 MB | |
| `.vcf.gz`, /dev/null, pinned, 3 rounds | 1.36 s, 562-600 MB | 1.29-1.31 s, 345-346 MB | |
| plain, file, unpinned, 3 rounds | 2.04-2.08 s, 655-671 MB | 1.84-1.93 s, 348-351 MB | |
| `.vcf.gz`, file, unpinned, 3 rounds | 2.02-2.17 s, 634-677 MB | 1.84-1.96 s, 349-351 MB | |

Peak memory falls from about 600 MB (560-680) to **344-351 MB**, steady from run to run (the
window classes no longer depend on thread timing). Time: the final build is as fast or faster in
every pair; these rounds ran while a reviewer's test job loaded the machine (load average about
6), so they are slower than this morning's for both builds. A second session (load average 1.9
rising to 8.7, the same review):

| run | base | final |
|---|---|---|
| plain, file, pinned, 5 rounds | 1.84-2.12 s, 600-609 MB | 1.78-1.87 s, 344-347 MB |
| `.vcf.gz`, file, pinned, 5 rounds | 1.81-1.90 s, 567-601 MB | 1.77-1.86 s, 344-350 MB |
| plain, /dev/null, pinned, 3 rounds | 1.31-1.35 s, 592-597 MB | 1.23-1.25 s, 344-345 MB |

So the final build is about 0.05-0.1 s faster (3-7%), less than the 0.2 s the no-copy prototype
showed: the real version does the swap test at every line and copies the last partial line of
each piece. Both sessions should be re-timed on a quiet machine before the numbers go in the
README's speed table (its memory figure is updated to about 350 MB).

Where the final build's memory goes (instrumented, 417 MB less 66 MB of instrumentation): the heap
320 MB, of it 4 MiB blocks 292 MB (73 at once: 32 VCF pieces, 16 in the batch and 16 read ahead;
up to 25 windows; 16 output buffers), smaller blocks 28 MB; outside the heap about 25 MB.

### The memory/speed setting for later: 1.6 MiB pieces

Final code with pieces of 1,677,721 bytes (`main.bend`'s `piece()`), plain, file, pinned, 3
rounds, same session: final 1.92-1.94 s, 344 MB; 1.6 MiB pieces 1.91-2.08 s, 231-232 MB; 1.6 MiB
pieces with `ahead()` = 2,031,607 (windows of 2 MiB) 2.08-2.14 s, 208 MB. That is about +5-10%
for -115 to -135 MB. Not applied.

## Rebased onto `threads` (2026-10-29)

`git rebase threads` onto f35ac0a (`--threads N`), then onto f73e77e (driver review 6: the
constructor rejects values of 2^48, comment rewraps): both applied with no conflict, and no fix
was needed. Each side's intent stays: `io64.c` has the variable read-ahead depth
(`IO64_AHEAD_MAX`), `IO64_FA_MAX` 128, the `BENDRTS` constructor and the 128 KiB stack buffer;
`norm.bend` has `kmax()` 128 (the driver closes a batch with an empty piece after every N pieces)
and the task without a copy; `build.sh` has the heap patch (threads did not change it); README and
`docs/DEVELOPMENT.md` have both sides' text.

Checks on the tree rebased onto f35ac0a (REF: f35ac0a built the same way, without `--threads`):
- the gate, through `test/bcheck.sh`: `PROOF.bend --check-only` and `--verdict` ALL PROOFS CHECK;
  `examples.bend` and `MACHINE.bend` 16 TODOs (the imported laws, `threads` included), `main.bend`
  79 defs rely on unsafe or foreign code (as on `threads`);
- at piece sizes 3,670,016, 70,001, 1,000 and 300: `same.sh` 128/128, `par.sh` 312/312,
  `test/threads.sh` (with `--threads 1, 2, 3, 7, 16, 32, 128` at three positions against REF
  without it) 2,128/2,128 with the usage errors OK and `BENDRTS` read, the gz suite 252/252, the
  end-of-file suite as expected (at 300 the same 8 known lines as the base build);
- whole genome `-c w` and `-c e`, plain and `.vcf.gz`: stdout, stderr and exit code identical to
  REF.

After the second rebase (onto f73e77e), as the lead asked: a rebuild and a smoke test only: chr22
and the scrambled file under `-c w`/`-c e`, with and without `--threads 4`, identical to f35ac0a's
build (8/8); `--threads 281474976710656` (2^48) stops as f73e77e's own build does ("bend: a Nat
past the largest immediate 2^48-1", exit 1).

Timings (whole genome, `-c w`, to a file, pinned 0-15, under the lock, interleaved, 3 rounds; each
run waited for the 1-minute load average to be under 2, and it was 1.5-1.95):

| build | time | peak RSS |
|---|---|---|
| `threads` (f35ac0a), default | 1.83-2.10 s | 541-550 MB |
| rebased, default | 1.75-1.76 s | 338-346 MB |
| rebased, `--threads 1` | 5.82-5.87 s | 43-44 MB |
| rebased, `--threads 2` | 3.81-3.94 s | 82-84 MB |
| rebased, `--threads 4` | 2.54-2.56 s | 129-132 MB |
| rebased, `--threads 8` | 1.97-2.14 s | 198-206 MB |
| rebased, `--threads 16` | 1.78-1.79 s | 336-342 MB |
| rebased, `--threads 32` | 1.69-1.71 s | 604-610 MB |

All 24 runs wrote the same output (xxh64 `3469a25b962abb21`). The default is 16 pieces per batch
and Bend's own thread count, which is the number of CPUs the process may use (16 here, pinned);
`--threads 16` matches it. Memory grows with N by about 18-20 MB per piece of a batch (the piece,
its read-ahead slot, its window and its output buffer, 4 MiB blocks each), plus about 25-45 MB.
`--threads 32` on 16 cores is 5% faster than the default for 75% more memory.

## For Bend upstream (draft; not posted)

**Title: CPU heap: large blocks freed on a worker thread are parked there and not reused, so a
program whose main thread allocates and whose tasks free grows by up to one block per thread and
block size**

*What happens.* In the C runtime (Bend 2.0.39, `bend file.bend -o file.c`), `heap_free` puts a
freed block on the freeing thread's free chain for its class. For classes whose keep limit
(`KEEP(c) = KEEP_WORDS >> c`, `KEEP_WORDS = 32768` on the CPU) is one block, i.e. blocks of
256 KiB and more, the chain reaches the limit at once and `heap_hand` runs: it pushes the
thread's previous parked ("cold") block to the shared bank and parks the new one as the thread's
cold block. So the block just freed stays with that thread until the same thread frees another
block of the same class. `heap_alloc_miss` takes only the allocating thread's own cold block or
a bank entry, then fresh memory from the bump pointer, which is never returned. When one thread
allocates large blocks and other threads free them (a value built and then consumed in parallel
tasks), up to one block per worker thread and per class stays parked, and the allocating thread
keeps taking fresh memory. Since memory is never given back and blocks are never split or
merged, the stranded blocks stay counted in the process's peak for the whole run.

*Minimal repro* (`data/tmp/mem/repro/strand.bend`):

    import Base

    # A block of 2^d words, all set.
    def blk(+d: Nat) -> Array<U32>:
      Array.new(U32, d, 7)

    # Reads one word of a block; the block is dropped (freed) here.
    def use.k(r: Array<U32> & U32) -> U32:
      (a, +w) = r
      w

    def use(a: Array<U32>) -> U32:
      use.k(Array.get(U32, a, 0))

    # n rounds: two blocks made on this thread, each dropped in its own parallel
    # task. At most a few blocks are live at once.
    def go(n: Nat, +d: Nat) -> U32:
      match n:
        case 0n:
          0
        case 1n+m:
          a = blk(d)
          b = blk(d)
          x y = use(a) use(b)
          (x + y + go(m, d) : U32)

    def main() -> U32:
      go(300n, 22n)

Built with `bend strand.bend -o strand.c` and `clang -std=c11 -O3 strand.c -lpthread -lm`, run
with `taskset -c 0-15` (x86-64, 32 hardware threads), peak RSS from `getrusage`, two rounds:

| build | 16 threads | `BENDRTS="--threads 1"` |
|---|---|---|
| as generated | 162-180 MB | 34-40 MB |
| with the patch below | 36-44 MB | 37-40 MB |

Each block is 16 MiB and about two are live at once; as generated, the 16-thread run commits
about ten. In a real program (framebender: 16 parallel tasks per batch, blocks of 2 to 32 MiB
allocated by the driver on the main thread and freed in the tasks) the stranded blocks were
about 80 MB of a 600 MB peak; with the patch the peak fell by about 85 MB, with no change in time.

*The patch* (what framebender's `build.sh` applies to the generated C): at the top of
`heap_hand`,

    if (KEEP(cls) == 1) {
      bank_push(e.mem, cls, ALC_AT(e, cls));
      ALC_AT(e, cls) = ALC_LEN(e, cls) = 0;
      return;
    }

For such a class the chain handed is exactly the block just freed (a one-block generation, as a
bank entry of that class is), so it goes to the bank at once, where any thread's next miss of the
class finds it. Smaller classes keep their per-thread chains. A fix in the runtime might also
consider handing a thread's cold blocks to the bank when it goes idle, or letting a miss take
another thread's cold block.

## Open questions for the driver review (runtime patch and buffers)

1. The runtime patch: is the argument above right (a one-block generation, the bank's
   capacity of two entries per possible block of the class, the bank lock), and are the
   build-time checks enough to refuse any other runtime? Any path where the patched `heap_hand`
   runs with a chain of more than one block?
2. 128 KiB of stack per reading thread (`pthread_create` with default attributes: the default
   stack size is the soft `RLIMIT_STACK`, or 2 MiB when unlimited), and on the calling thread when
   a thread cannot be created. Enough margin?
3. With smaller windows, a damaged FASTA is met at a different read, so the output written before
   the error differs in length (still a prefix of the good output, same error). Acceptable?

## Scratch (`data/tmp/mem`)

`patch_mem.py` (instrumentation), `var.py` and `mk.sh` (variants of the generated C; `X_i` is
the instrumented build of `X`), `run.py` (time and peak RSS), `bench.sh` (interleaved runs under
the lock), `bench*.txt` (every timing above), `log_*.txt` and `*.smaps` (instrumented runs),
`wants.txt` (every FASTA read's size), `t_*` (edited copies of the tree: `nocopy`, `cap`,
`cap_a`, `cap2_a`, `nccap_a`, `nccap2_a`, `k8`, `nc_k8`, `nc_k32`, `ahead`), `st`, `st_a` (the
sequential machine with today's driver), `g_*.c`, `fb.c`, `fbseq*.c` (generated C).
