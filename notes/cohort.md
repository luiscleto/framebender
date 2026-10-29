# Cohort VCFs (phase G): where the time goes, and the options

Brief: `notes/briefs/COHORT.md`. Branch `cohort`, on 64c37ad. Steps 1 and 2 only: nothing
implemented outside `data/tmp/cohort/` (scratch), nothing committed.

All timings: `data/tmp/cohort/bench.sh` (interleaved, `flock data/tmp/bench.lock`, `nice -n 19`,
`taskset -c 0-15`, a timeout; wall, user, sys and peak RSS from `os.wait4`), output to /dev/null
unless said, 2-3 rounds, machine otherwise idle (load average under 1). "cur" is main's build
(`./build.sh` steps, `data/tmp/cohort/fb_cur`). Inputs: `data/kg/sub.vcf` (1000 Genomes chr22, 800 MB,
57,534 records of about 13.9 KB, already normalized) and, for comparison, `data/tmp/cohort/giab_800.vcf`
(the first 800 MB of `data/hg002.all.vcf`, cut at a line end: 1,134,147 records).

## Summary

The time is not in reading long lines: the machine handles cohort lines at 1.8 GB/s on one core.
It goes into the **sorting buffer at the default `-w 100000`**. An item stays buffered until a
line's input POS reaches its key + w (run.bend's `ready`). chr22 of the 1000 Genomes panel has
about 25 records per kb at 13.9 KB each, so 100 kb of genome is 43 MB of buffered text on
average (93 MB at most), against about 14 KB on GIAB. Two consequences:

1. **Every step copies the whole buffer.** `NR.take` (the end of a step) hands out `ob` and copies
   the buffered texts into a new block, sized to them and zero-filled by `Array.new`. A step
   happens about once per piece. On `sub.vcf` that is 165 steps with 43 MB each: **7 GB copied,
   about 14 GB zero-filled**, and about 30 regrowths of the buffer (`BY.grow`, a word at a time).
   This is about 87% of the CPU time.
2. **No piece merges.** `merge.ok` needs the true run's buffer E to be all written within the
   piece (a line with input POS at least max(E) + w). A 3.5 MiB piece of cohort lines spans about
   10 kb < w, so every piece fails the check and goes to the sequential machine. Each line is
   judged twice (once in its task, uselessly, once sequentially), and nothing runs in parallel.

The memory comes from the same buffer: its blocks go through the 32, 64, 128 and 256 MiB size
classes, and Bend's heap keeps each class's own peak (744 MB committed, about 200 MB live at any
moment).

With a smaller window both effects vanish and the output does not change on this file:
`-w 1000` (the size of bcftools' default `--site-win`) runs `sub.vcf` in **0.17 s, 227 MB**,
against cur's 3.07 s and bcftools' 3.1-3.4 s. The body is byte-identical to the default run's and
to the input. **The default w is the law's (`types.bend`: `B.Args`, default 100000).** Changing
it is a law change, outside this brief: I only flag it. The machine options below keep w as it is.

## Step 1: where the time and the memory go

### Method

Scratch instrumentation of the generated C (`data/tmp/cohort/`, none of it tracked):
- `patch_prof.py`: a counter at the entry of every Bend def (each `WL_CASE`, per thread, summed at
  exit), and a SIGPROF sampler (ITIMER_PROF, process CPU time, about 1 ms per sample in practice)
  recording each sample's PC. `sym.py` maps PCs to C functions (`nm` on a `-no-pie -g` build).
  `cats.py` groups them into stages; a `spin_N` helper is charged to the Bend defs that call it
  (traced through the generated C).
- `patch_sizes.py`: big blocks made per size class (`blk_new`, 1 MiB and up), `BY.grow` calls per
  class, and per step `NR.take`'s written bytes (ow) and kept tail.
- `../mem/patch_mem.py` (the memory agent's): heap committed and live per class.
- `mk.sh tree out [prof]`: builds a tree as `build.sh` does (heap patch), optionally instrumented.

### Counts on `sub.vcf` (default threads; the same at `--threads 1`)

| | count |
|---|---|
| records | 57,534 |
| lines on the fast path (`NR.fast_done`) | 114,223 (each record twice: its task, then the sequential machine) |
| lines judged as String (`norm_seq.line` / `J.judge_fs`) | 216 / 105 (header and the line across each boundary) |
| batched pieces (`merge.ok` calls) | 217 |
| pieces merged | 0 (the sequential machine pumps 57,615 lines, about every record) |
| steps (`Norm.step`) | 465 |
| `NR.take` steps that copy a tail | 165: 754 MB written, tails **7,032 MB** in total, 43 MB on average, 93 MB at most |
| new blocks of 32 / 64 / 128 / 256 MiB | 45 / 70 / 52 / 4 (zero-filled by `Array.new`) |
| `BY.grow` of the buffer to 16-256 MiB | 29 (word by word) |

With `-w 1`: 57,481 fast-path lines (once each), 389 lines pumped sequentially, every piece
merged, 16 tail-copying steps with tails of 0 MB. On `giab_800.vcf`: 1,136,428 fast-path lines,
the same 217 pieces, 20 tail-copying steps with 1 MB of tails in all.

### Where the time goes

`--threads 1` (one core, so the stages add up to the wall time; 3.43 s wall, 3.47 s user+sys,
1,538 samples spread over the CPU time):

| stage | CPU | share |
|---|---|---|
| step end: new block for the buffer, zero-filled (`NR.take` → `BY.empty`) | 1.19 s | 34% |
| byte copies (`F.append`): the buffer's tail at each step end (about 0.95 s), the records into the output buffer | 1.04 s | 30% |
| buffer growth (`BY.grow` from `NR.room` / `NR.reserve`, word by word) | 0.63 s | 18% |
| per-line machine (fast path, flush, insert), for each line twice | 0.31 s | 9% |
| libc and kernel entry (reads, writes), reference counts, other | 0.29 s | 8% |

Default threads (3.05-3.11 s wall, 4.1 s user+sys): the same shares (take 37%, copies 31%,
growth 18%, per-line 6%). The tasks run in parallel, but the step ends, the growth and the
second judging of every line are all in the sequential machine, which is the wall time.

Same-size GIAB slice at `--threads 1` (1.55 s): per-line machine 48%, libc/kernel 17%, other 17%,
copies 8%, growth 7%, step ends 1%. There the cost is per record (1.13 M records); on cohort
lines it is per step, times the buffer's size.

| run | wall | user | sys | peak RSS |
|---|---|---|---|---|
| cur, `sub.vcf`, default | 3.05-3.11 s | 3.66-3.75 | 0.35-0.39 | 976-978 MB |
| cur, `--threads 1` | 3.43-3.44 s | 3.18-3.24 | 0.25-0.29 | 780 MB |
| cur, `-w 1` | 0.16-0.17 s | 0.94-0.95 | 0.19-0.21 | 225 MB |
| cur, `-w 1 --threads 1` | 0.43-0.44 s | 0.41-0.42 | 0.09-0.10 | 34 MB |
| cur, `-w 100` / `1000` / `10000` | 0.17 / 0.17-0.18 / 1.31 s | | | 224 / 229 / 406 MB |
| bcftools 1.24 (default; `-w 1000` the same) | 3.11-3.44 s | 2.98-3.34 | 0.09-0.12 | 12 MB |
| cur, `giab_800.vcf`, default / `--threads 1` | 0.37-0.38 / 1.54-1.58 s | 2.78-2.91 / 1.34-1.36 | | 310 / 42-46 MB |
| bcftools, `giab_800.vcf` | 1.59-1.67 s | | | 12 MB |

So on one core with a small window, cohort lines run at 800 MB / 0.44 s = 1.8 GB/s, against
0.5 GB/s for the GIAB lines of the same size. The brief's suspects, checked:
- the fast path refusing cohort lines: no, it takes all but the header and boundary lines;
- the batches falling back: yes, all of them (`merge.ok`'s "E written within the piece");
- the line across a boundary: 217 String judgements, negligible;
- the runtime's cost per byte on long lines: no (1.8 GB/s);
- the reference windows: negligible (217 pieces, small windows).

### Where the memory goes

`patch_mem.py` on cur, `sub.vcf`:

| | `--threads 1` | default |
|---|---|---|
| peak RSS | 828 MB | 1,014 MB |
| heap (bump pointer) | 767 MB | 960 MB |
| 8-256 MiB blocks: the run's buffer (committed per class: 8 + 32 + 64 + 128 + 256 + 256 MB) | 744 MB | 744 MB |
| of which live at the peak | 192 MB | 192 MB |
| 4 MiB blocks (pieces, read-ahead, task outputs) | 20 MB | 196 MB |

The buffer is up to 93 MB of text, but each step's new block is sized to the current tail
(plus the input left, plus 64 KiB, rounded up to a power of two), so the buffer moves between
classes as the tail grows and shrinks. Each class keeps its own peak: two 64 MiB blocks, two
128 MiB, one 256 MiB, ... all committed.

## Step 2: options

Every prototype is a scratch tree in `data/tmp/cohort/t_*`, type-checked with `test/bcheck.sh` (79 defs rely
on unsafe or foreign code, as main) and checked against cur with `cmpr.sh` / `cmpset.sh`
(stdout, stderr and exit code). The checks were on `sub.vcf`, `giab_800.vcf`, `data/scr.vcf` and
`data/hg002.chr22.vcf`, under `-c e` and `-c w`, and for B also at `-w` 50 and 10,000: all
identical. The suites (`same.sh`, `par.sh`, tiny pieces, gz) were not run on prototypes.

### Driver only: larger pieces (measured; not recommended)

Fewer steps, and pieces long enough to span w. The piece size replaced in the generated C:

| build | `sub.vcf` | `giab_800.vcf` |
|---|---|---|
| cur (3.5 MiB) | 3.07-3.10 s, 976 MB | 0.37-0.38 s, 310 MB |
| 14 MiB pieces | 1.58-1.60 s, 1,508 MB | 1.58-1.59 s, 947 MB |
| 28 MiB | 1.33-1.34 s, 2,195 MB | |
| 56 MiB | 0.91-0.92 s, 2,224 MB (`--threads 4`: 0.86 s, 1,382 MB) | 2.17-2.21 s, 1,582 MB |

On GIAB, pieces spanning more than a 4 MiB window go dirty, so the driver would have to pick the
size from the data (bytes per base), and memory still grows by about 3 blocks per piece in
flight. Dominated by A below.

### A. Machine: a step end that costs what it writes (prototyped)

`NR.Run` gets one more field, `oz`: ob is [dead 0..oz | written oz..ow | buffered ow..len]. At a
step end:
- nothing dead and the tail no longer than the written bytes: as now (ob handed out, the tail
  copied to a new block);
- otherwise the written bytes are copied to a new block, the step's output;
- ob is kept (oz = ow) while the tail is longer than the dead bytes and the next piece fits;
- else it is compacted: the tail copied to a new block of twice its size, plus the input left.

So each byte is copied out once, and the tail is copied about once per tail's worth of output.
The merge hands out S's ob from oz (`NR.out_from`). Code: `data/tmp/cohort/t_take/norm_run.bend`
(about 90 lines: `take.*`, `out_from`), `oz` added mechanically to the 92 `Run{...}` sites
(`addfield.py`), two sites fixed by hand.

| run | cur | A |
|---|---|---|
| `sub.vcf`, default | 3.05-3.10 s, 976 MB | **1.16-1.20 s**, 1,106-1,107 MB |
| `sub.vcf`, `--threads 1` | 3.43 s, 780 MB | 1.53-1.54 s, 911 MB |
| `giab_800.vcf`, default | 0.37-0.38 s, 310 MB | 0.38-0.39 s, 310 MB |

A first version that always kept ob (never compacting while the tail was long) ran in 1.29-1.33 s
with 1.44 GB. A version that also kept ob when the tail was short crashed: once ob reached 2^29
bytes the machine switched to its String mode (`to_ms`), which reads ow as "bytes written". So
the String-mode switch and the 2^30 Yield must count ow - oz; a real version must state that.

What is left in A (`--threads 1`, 1.5 s): zero-filling the compaction blocks 17%, copies 20%,
regrowth 18%, the per-line machine (each line twice) 16%, libc 9%. Memory is no better: the
compaction blocks still change class. **A' (not measured):** compact in place, moving the tail
to the front of the same block, with a word-at-a-time overlapping move. Then there is no new
block, no zero-fill and no class change. Memory would be about one block of twice the tail,
plus today's pieces. That needs a new `lawful-bytes` operation (a fast `shift`, proven equal to
`bytes.bend`'s `shift` as `fast.append` is to `append`); today's `BY.shift` goes byte by byte.

Proofs (A or A'): no law changes. `NR.Run`'s refinement (`to_spec`: the written text becomes
ob[oz..ow)); the take lemmas (`proof_b_run_take`, and its users `proof_b_run`, `proof_b_bud_out`,
`proof_b_bud_hop`, `proof_b_drive_out`, `proof_b_drive_fin`, `proof_e_wrap_base`,
`proof_e_wrap_qx`); the bounds (each output under 2^31 bytes, Yield and the String-mode switch on
ow - oz); and the merge's output (`proof_e_merge*`, `proof_e_wrap_mok`: S's output from oz). Plus
the field itself in the 16 proof files that take `NR.Run` apart (about 40 patterns, mostly
`proof_b_run_*`). My guess: about the size of the memory phase's no-copy (800 lines), mostly in
phase B's run proofs.

### B. Machine: a deferred merge (prototyped on top of A)

A clean task that wrote nothing (its last is still the phantom), in S's CHROM run, with every
key at least l and E's keys at most l, is spliced in even when E is not all written. The true run
writes E's ready prefix (key + w at most the largest input POS of the task's lines; E is
sorted, so these items are a prefix and are written in order). Its buffer becomes the rest of E,
then the task's buffer (lines shifted), and the task's texts are appended to S's ob. Then an
ordinary `NR.take`. Why it is the true run: every task key is at least l, which is at least
max(E), so a task item becomes ready only after all of E. The task wrote nothing, so no task item
was ready at any of its lines. Inserting a task item puts it after all of E, so the buffer is
E's rest followed by the task's buffer, in the task's order. Code:
`data/tmp/cohort/t_merge/norm.bend` (`merge.ok2`, `rdy_*`, `merge.d.*`, about 70 lines).

| run | A | A + B |
|---|---|---|
| `sub.vcf`, default | 1.18-1.21 s, 1,108 MB | 1.12 s, 1,106 MB |
| `--threads 1` / `--threads 4` | | 1.40-1.41 / 1.22 s |
| `-w 10000` | | 0.74 s (cur 1.31 s) |
| `giab_800.vcf` | | 0.38 s, 310 MB |

The merges now happen (the sequential machine pumps 389 lines, each line is judged once), but
it gains only 5%. About 70% of what remains is the buffer traffic in the sequential machine:
each piece's texts are appended to the true buffer, copied out at the step end, and compacted.
B pays off only once that traffic is gone. Proofs: `merge.ok`'s new case and the segment lemma
for a buffer not all written (area B and C of phase E: `proof_e_seg*`, `proof_e_merge*`, about
5,400 lines, which assume E is all written), plus `proof_e_wrap_mok` and `_mc`. A large job,
the size of a phase-E area or two.

### C. Machine: the buffer as a queue of blocks (not prototyped)

To approach the `-w 1000` speed (0.17 s) at w = 100000, the sequential machine must stop moving
the buffered bytes. Each task's output block would join a queue, and a step would hand out a
block once all its items are written: zero copies, since items are written in key order, which
is block order unless a record moves left across blocks (then copy, as today). This changes
`NR.Run`'s representation and the merge: the largest proof job of the three. An estimate only.

## Recommended order

1. **The default window (owner's call; a law change, so I stop there).** On cohort files the
   default w is the whole problem. `-w 1000` already gives 0.17 s and 227 MB on `sub.vcf` (18×
   bcftools), with identical output on this file. Users can pass `-w` today; a README sentence
   would be a documentation change only.
2. **A' (in-place compaction):** no law change, about one phase B area of proofs, plus a
   `lawful-bytes` fast `shift`. Measured as A: 3.1 → 1.2 s on `sub.vcf`; A' should also cut the
   zero-fill and the memory (not measured). Neutral on GIAB. I would prototype A' first, to
   measure it before the proofs.
3. **B, then C, only if the default-w cohort speed still matters after 1 and 2.** B alone gains
   5% on top of A. B with C is the route to parallel cohort runs at w = 100000, and the largest
   proof job.

## Scratch (`data/tmp/cohort`)

`patch_prof.py`, `patch_sizes.py`, `sym.py`, `cats.py` (instrumentation), `mk.sh` (builds),
`run.py`, `bench.sh`, `cases*.txt` (timings), `cmpr.sh`, `cmpset.sh` (output comparisons),
`addfield.py`, `t_take` (A), `t_merge` (A + B), `fb_cur`, `fb_take3` (A as measured),
`fb_merge`, `fb_p16`/`p32`/`p64` (larger pieces), `prof_*.txt`, `mem_t*.txt`, `giab_800.vcf`
(800 MB; delete when done).
