# `--threads N`: brief for the threads agent (phase F)

Goal: one option, `--threads N` (the name bcftools uses), so a user can tune framebender to their
hardware: fewer threads and less memory on a small machine, more on a large one. The owner: "the
configuration is important for fine tuning on different hardware"; N may be above 16 (no upper
limit beyond what is sane to state).

## What exists

- The batch size is `kmax()` in `norm.bend` (16). No proof uses its value: it appears only in
  the test that closes a batch (`Nat.is_le(W.kmax(), 1n+k)`, in `proof_e_bud_phase.bend`,
  `proof_e_wrap.bend`, `proof_e_wrap_col.bend`), so any value from 1 up should keep the proofs.
- Bend's runtime picks its worker threads before the program starts: the CPU count, or
  `BENDRTS="--threads N"` / `+RTS --threads N -RTS` (see `CLI_HELP` and `main` in any generated C
  file). The laws never see it, and it cannot change the output.
- The driver has its own fixed depths: `IO64_AHEAD 16` (VCF read-ahead) and `IO64_FA_MAX 32`
  (reference reads in flight), both in `io64.c`.
- The command line is parsed by `B.Args.parse` in `types.bend` (science layer) into
  `B.Opts{strict, w, args}`; `law machine` (`MACHINE.bend`) states the output as
  `L.run(fasta, vcf, o)`, and `law usage` makes any command line `parse` refuses a usage error.
  `o.args` is printed in the header (`##framebender_normCommand`).

Lead's measurements (whole genome, to a file, pinned; identical outputs): batch 1 / 4 / 8 / 16:
3.9 / 2.6 / 2.1 / 1.8 s; batch 32 was 2-3% faster than 16 at 780 MB. Memory is mostly not the
batch (the memory agent works on that, see `notes/briefs/MEMORY.md`).

## Steps

1. **Design and draft the law change; then stop.** A change to the science layer and the
   contract needs the three-model law review (the lead runs it) and later the owner's sign-off.
   Propose, in `notes/threads.md`:
   - the option's syntax and range, its default (today's behaviour), and where N goes: the
     batch size, the runtime threads, the driver's depths (how the runtime's thread count can
     follow the option without a fragile hack, or why it should not);
   - the exact edits to `types.bend` (`Args.parse`, `Opts`, `usage`), `LAWS.bend` and
     `MACHINE.bend`, as a diff; keep them minimal;
   - a law that says N never changes the result, for example that two runs whose options differ
     only in N give the same output apart from the command line printed in the header, stated so
     a reviewer sees it at once;
   - what the proofs and examples need (`examples.bend`, `examples_machine.bend`, `PROOF.bend`),
     and the expected size of the work.
   Print the draft and stop.
2. After the review (the lead's message): implement, prove, check, time; then report and stop.

## Rules

- Work in your own worktree (`../framebender-threads`, branch `threads`); `data` there links to
  the main checkout's `data`, so the big inputs and `data/tmp` are shared: put your scratch files
  in `data/tmp/threads/`. Another agent works on branch `memory` at the same time and may change
  the same driver files: do not touch its worktree.
- Fixed until the review: everything except your notes. `../lawful-*` stay fixed.
- Every `bend` check through `test/bcheck.sh` (4 GB, at most two at once across all agents).
- **Timing runs: one at a time across all agents**: `flock data/tmp/bench.lock ...`, `nice -n
  19`, a `timeout`, pinned (`taskset -c 0-15`), interleaved, ranges; delete each output file
  before the next timed run. Peak RSS from Python's `resource.getrusage(RUSAGE_CHILDREN)`.
- `BEND_NO_TELEMETRY=1`. No commits, pushes or branch switches; the lead commits.
