# Moving the proofs to the two-layer spec: brief for the migration agent

Read `PROVING.md` first (layout, Bend proof notes, rules). Work on the git branch `two-layer`
(already checked out; do not switch branches, do not commit: the lead commits).

## What changed (approved by the reviewers: `reviews/responses-6.md`, `reviews/*-d3.md`)

The spec now has two layers:
- Science (frozen once approved; never edit): `LAWS.bend` (13 laws: `sorted`, `grouped_in`,
  `no_unsorted`, `twice_run`, `normalized_valid`, `same_change`, `stays_valid`, `standard_form`,
  `normal_unchanged`, `twice`, `one_form`, `shortest`, `unique`), `types.bend`, `run.bend`, and
  `tan.bend` (the reference normalizer `Tan.normal`; identical code to the old `norm_var.bend`
  apart from the module name and `var` renamed `normal`). `judge` (and so `run`) now calls
  `Tan.normal`, and the variant laws are about `Tan.normal`, not `Norm.var`.
- Implementation (also frozen): `protocol.bend` (`P.Ans` = `Unknown | Known` (no `NoAns`), `P.Req`,
  `P.In` = `Chunk | Eof | Ref{ans: List<Ans>}`, `P.Next` = `More | Ask{reqs: List<Req>} | Finish`,
  `P.Fasta.plain`) and `MACHINE.bend` (`truth`, `truths`, the driver definition with a read counter,
  `bound`, `launch`; laws `machine` (new premise `P.Fasta.plain(fasta)`) and `usage`).
- The window laws are gone as laws; their content survives as lemmas of the implementation proof.
- `draft/` holds the reviewed copies; the root files are now those copies.

## Your job

1. Adapt the code to the new interface with minimal changes (keep the current sequential design;
   a separate agent will make it batched and parallel afterwards):
   - `norm_line.bend`: `judge_in` takes a `Maybe<&2, P.Ans>` (None = nothing read) instead of `NoAns`.
   - Replace `norm_var.bend` by calling `Tan` directly (`Tan.var_in`, `Tan.normal`); delete
     `norm_var.bend` (the spec normalizer is the code's normalizer now).
   - `norm.bend`: protocol types from `protocol.bend`; ask a list of one read (`P.Ask{[P.Req{..}]}`),
     take the first answer of `P.Ref{ans}`. Keep `Norm.var` only if something still needs it.
   - `main.bend` (trusted driver): answer every read of an `Ask`, in order. Keep it simple and
     obviously right; it will be reviewed as trusted code.
2. Move the proofs: `PROOF.bend` must import `LAWS.bend` and `MACHINE.bend` and prove every law of
   both (`def L.name` / `def M.name`). The var proofs retarget from `V`/`Norm.var` to `Tan`; the new
   `unique` is the uniqueness the var area already proved; `normalized_valid` follows from the
   window area's validity lemmas (`valid_of`); the old window laws become lemmas about `judge_in`;
   `twice_run` uses the var laws about `Tan.normal`; the machine proof follows the protocol change
   (lists of reads, the read counter within `bound`, the `Fasta.plain` premise is unused unless
   helpful).
3. `./check.sh` must end with ALL PROOFS CHECK twice (bend and `--verdict`); `examples.bend` must be
   updated to the new names where needed (expected values unchanged) and pass; the output must stay
   byte-identical: `test/compare.sh data/chr22.fa data/hg002.chr22.vcf` and
   `test/compare.sh data/chr22.fa data/scr.vcf` (0 differing records),
   `test/compare.sh test/edge/ref.fa test/edge/sorted.vcf` (exactly 1, the `<DEL>` record).
   Build: `timeout 1200 env BEND_NO_TELEMETRY=1 nice -n 19 bend main.bend -o framebender`.
4. You are the only agent running; benchmarks are not your job (do not time things).
5. Keep `notes/migrate.md`: what moved, what needed real work, where it got hard (research data:
   what it cost to restructure the laws of a proven project).
