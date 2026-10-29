# Memory: brief for the memory agent (phase F)

Goal: bring framebender's peak memory on the whole genome from about 600-670 MB down towards the
sequential machine's 140 MB (bcftools 1.24: 11 MB), keeping most of the speed (1.8 s now; 4.7 s
sequential; bcftools 7.9 s). The owner: "using 60x what bcftools uses is a bit over the top",
and "ultimately speed is more important". So speed comes first: prefer savings that cost no
time; list any that cost more than about 3% separately, as a trade-off for the owner (or for the
`--threads` option, which another agent is designing), never as the default.

## What the lead measured (whole genome, -c w, to a file, pinned, all outputs identical)

| build | time | peak RSS |
|---|---|---|
| sequential machine (norm_seq.bend as the machine, old driver) | 4.7 s | 140 MB |
| parallel, batch of 1 piece (`kmax` 1) | 3.9 s | 460-630 MB |
| batch 4 / 8 / 16 (now) | 2.6 / 2.1 / 1.8 s | 490-530 / 460 / 600-670 MB |
| batch 16, driver read-ahead `IO64_AHEAD` 4 / 1 instead of 16 | 1.9 / 2.0 s | 530-550 / 500-540 MB |
| batch 16, `BENDRTS="--threads 1"` (runtime threads) | slow | 430 MB |

So neither the batch size nor the thread count explains it: even one piece per batch on one
thread costs about 300 MB more than the sequential machine. Suspects, unverified: per-piece
buffers (the piece's copy, its reference window, its output buffer, Q's fresh state per task)
rounded up to power-of-two blocks; Bend's heap, which never shrinks and keeps freed blocks per
size class (the runtime's C is in the generated file: `heap_alloc`, `heap_free`, `corpus_grow`).

## Steps

1. **Find where it goes.** Instrument a scratch copy of the generated C (never the tracked
   files): log allocations above some size by class and call site, the heap's high-water mark,
   and RSS over time; compare the sequential and parallel builds. Report a breakdown that adds up
   to the measured peak.
2. **Options**, each with the measured saving and time cost, and what it costs to make:
   - driver only (trusted: `main.bend`, `io64.c`, `io64.js`, `build.sh`; needs a three-model
     driver review, no proofs);
   - machine changes (`norm.bend` and its helpers; outputs must stay identical; proofs must be
     redone where they change; say which proof files and roughly how much);
   - runtime settings (anything the runtime offers, e.g. heap size or growth).
   The earlier trade: dropping the per-piece copy saves memory but adds a proof obligation (the
   piece must still be in Q's input at every early exit; `notes/parallel.md`).
3. **Report and stop** with the breakdown and a recommended order. Do not implement beyond
   scratch prototypes until the lead answers.

## Rules

- Work in your own worktree (`../framebender-mem`, branch `memory`); `data` there links to the
  main checkout's `data`, so the big inputs and `data/tmp` are shared: put your scratch files in
  `data/tmp/mem/`. Another agent works on branch `threads` at the same time and may change the
  same driver files: do not touch its worktree.
- Fixed: the science layer, the contract (`protocol.bend`, `MACHINE.bend`, `bytes_enc.bend`), and
  `../lawful-*`.
- Every `bend` check through `test/bcheck.sh` (4 GB, at most two at once across all agents).
- **Timing and memory runs: one at a time across all agents.** Wrap every timed or measured run
  in `flock data/tmp/bench.lock ...`, with `nice -n 19`, a `timeout`, pinned (`taskset -c
  0-15`), interleaved, with ranges. Delete each output file before the next timed run (the shell
  truncating an old 2.8 GB output is otherwise counted). Peak RSS:
  `resource.getrusage(RUSAGE_CHILDREN).ru_maxrss` from Python (`time` is not installed). Keep at
  least 8 GB of RAM free.
- `BEND_NO_TELEMETRY=1`. No commits, pushes or branch switches; the lead commits.
- Notes in `notes/memory.md`.
