# The parallel machine: brief for the phase E coordinator

Your own plan is the design: `notes/speed_plan.md`, section "D. The parallel machine", and
"Recommended order" steps 3-4. The lead accepted it with these decisions:
- No contract change. If the design turns out to need one, stop and ask.
- The segment lemma (`run.go(lines, RS) == shift(RS, run.go(lines, RS0))` under `Pre`) and
  `Pre`/`shift` stay internal to the proofs: they are proven, so they need no review.
- `lawful-halves` is a new package with its own laws (a parallel map over a balanced tree), so its
  laws need the three-model review, and later the owner's sign-off.
- Batches of K = 32 pieces (about 400 MB) are fine.

## Steps

1. **`lawful-halves`** in `../lawful-halves` (a new local directory with `git init`, laid out like
   `../lawful-arrays`: `LAWS.bend`, `defs.bend`, the code, `PROOF.bend`, `check.sh`, `test/`,
   `docs/LAWS.md`, `README.md`, MIT `LICENSE`). Draft `LAWS.bend` and `docs/LAWS.md`, then print
   them and stop: the lead runs the three-model law review before the proofs.
2. **Prove `lawful-halves`** after the review (its `check.sh`: `bend` and `--verdict`).
3. **The parallel machine** on the branch `parallel` of framebender: the plan's steps 1-6 (collect,
   plan, one batched `Ask`, judge in parallel, combine in order with the sequential fallback,
   hand out the output). Code first, with identical outputs and timings; then the proofs, with
   sub-agents through Herdr as you see fit (each in its own workspace, closed when done).
4. **Parallel reference reads in the driver** (trusted code: the lead runs a driver review).

Report and stop after step 1, and after the code in step 3 (before the proofs at scale), with
timings, so the lead can check direction.

## Rules (as before)

- Fixed: the science layer, the contract (`protocol.bend`, `MACHINE.bend`, `bytes_enc.bend`), and
  `../lawful-words`, `-arrays`, `-bytes`, `-fields` (ask for anything new there).
- Every `bend` check through `test/bcheck.sh` (4 GB, at most two at once across all agents). Never
  close a goal about a big `Nat` by computation.
- Timing: `nice -n 19`, a `timeout`, one benchmark at a time across all agents, interleaved with
  bcftools, pinned (`taskset -c 0-15`) with unpinned ranges beside them.
- Checks: `test/same.sh` (all identical to `main`'s build), `test/compare.sh` (chr22, scr, edge,
  whole genome plain and `.vcf.gz`), the gz suites, the tiny-limit builds, and the gate's four
  steps. Add cases for the batch boundaries: a CHROM change at a piece boundary, a record moving
  left across a boundary, unsorted input, `-c e` stops in the middle of a batch, warnings under
  `-c w`, files shorter than one batch.
- Git: work on `parallel` (the lead creates it); no commits, pushes or branch switches; in
  `../lawful-halves`, `git init` only, no commits (the lead commits).
- Notes in `notes/parallel.md` (and `../lawful-halves/NOTES.md`).
