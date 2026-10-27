# Migration to the two-layer spec (branch `two-layer`)

Status (2026-10-27, about 16 minutes of wall time, one agent): **done**. `./check.sh` ends with
ALL PROOFS CHECK twice (bend, then `--verdict`); `examples.bend` passes with unchanged expected
values; `PROOF.bend` imports `LAWS.bend` and `MACHINE.bend` and proves all 13 + 2 laws.
Output: `test/compare.sh` gives 0 / 0 / 1 (the `<DEL>` record) differing records, and the new
binary is byte-identical (stdout, stderr, exit code, with and without `-c w`) to the binary built
from `cd68ea6` on all three inputs.

## What moved (mechanical)

- `norm_var.bend` deleted. Each `proof_var_*.bend` file changed one import line
  (`./norm_var.bend` -> `./tan.bend`, same alias `V`); `V.var` / `Norm.var` became `V.normal` /
  `Tan.normal` (proof_var 16 places, proof_window 7, proof_run_line/rejudge 5, proof_machine_ask 1).
  Since `tan.bend` is the old code verbatim, none of the var proofs needed a change.
- `unique`: a one-line forward to `proof_var_uniq.uniq`, the uniqueness lemma the var area
  had already proven (same statement, same hypothesis order).
- `twice_run`: unchanged; it calls the var proofs (`PV.twice`, ...), now about `Tan.normal`.
- Window laws -> lemmas: their definitions (`known.ok`, `truthful`, `chrom_of`, `covers`,
  `is_known`, `is_unknown`, `enough.go`, `enough`) moved from the old LAWS.bend to
  `proof_window_defs.bend` (alias `WS`), retyped for `Maybe<&2, P.Ans>`. A script rewrote the
  proofs: `B.Ans` -> `Maybe<&2, Pr.Ans>`, `B.NoAns{}` -> `None{}`, `B.Known{..}` ->
  `Some{Pr.Known{..}}` (brace-balanced), in patterns and terms alike. Nested patterns
  (`case Some{Pr.Known{+clen, +off, +raw}}:`) worked in the existing proof matches as they were:
  no proof in proof_window.bend needed a manual edit.
- Machine names: `L.truth` -> `Some{M.truth(..)}` (the answer is now a Maybe),
  `L.DSt/absorb/dstep/drive/result/bound/launch` -> `M.*`, `B.More/Ask/Finish/Ref` -> `Pr.*`.
- `usage`: the old `L.usage` proof, moved to proof_machine.bend as `M.usage`.

## Code changes (behaviour unchanged)

- `norm_line.bend`: `judge_in`, `judge_fs`, `judge_in.go`, `judge_in.ans` take
  `Maybe<&2, P.Ans>` (None: nothing read); imports `tan.bend` for `V.var_in`.
- `norm.bend`: `Norm.var` removed (nothing needed it; examples call `Tan.normal`). `Want`
  becomes `P.Ask{[P.Req{c, from, upto}]}`; `P.Ref{as}` is resolved with `first(as)` (the first
  answer, None for an empty list); `grow` and `resolve` take the Maybe. The machine still asks one
  read at a time.
- `main.bend` (trusted): `answers(rs, fai, fa)` answers every read of an Ask, in order, with the
  same `answer.got` as before, and the loop steps with `P.Ref{list}`. Three small defs
  (`answers`, `answers.k`, `answers.cons`), each one match.

## What needed real work

- `normalized_valid` (new, about 95 lines at the end of proof_window.bend): walk `L.judge`
  (`nv.shape` -> `nv.contig` -> `nv.bases` -> `nv.checks`); every outcome but Normalized is
  refuted by `is_normalized` computing False; in the Normalized case the checks give POS != 0,
  ALT distinctness and the REF match, and the not-MALFORMED lemmas give REF/ALT non-empty, so
  the window area's `valid_of` applies. Trick: `nv.checks` takes the four check results as Bool
  parameters with equations, so the caller instantiates them with the real expressions and `{==}`;
  the hypothesis `h` then has the right type by conversion, no rewriting.
- Machine proof (`proof_machine_sim.bend`, about 300 lines changed): the protocol change itself
  was cheap; the read counter was not.
  - Lists of reads: `Good` on an `Ask{qs}` goes through a new `GQ`, which is Empty unless `qs` is
    one read; `need` ignores the list. `STEP` and `Z` got two more absurd cases (`Ask{Nil{}}`,
    `Ask{Req{..} <> y <> t}`). The second must spell out `Pr.Req{c1, a1, b1}`: with a bare
    variable head, `GQ`'s nested pattern would not reduce to Empty.
  - The read counter: `DSt` has a new field, so every lemma that builds a driver state (`PD`,
    `AD`, `CD`, `WD`, `fin_k`, `FING`, `fin_ok`, `TLG`, `TL`, `PLG`, `PL`, `AskG`, `AS.k`, `AS`,
    `MoreG`, `MS.k`, `MS`: 17 of them) takes a new `rd` parameter, threaded by a script
    (inserting an argument at the position of `O` in every call needs a parser that knows
    `List<&2, ..>` commas from argument commas and `<>` from `<`/`>`). Inside the Ask step the
    state after the step carries `Nat.add(rd, 1n)` (`List.length` of a one-read list reduces).
  - The bound: `STEP` now also returns `reads(dstep d) <= 1 + reads(d)` (`STR`; lemmas
    `absorb_le`, `more_le`, `ask_le`); the invariant is `OkR` = `Ok` and
    `reads + fuel <= lim`, kept by `reads_step` (arithmetic), and `Z` reads off
    `reads <= lim` to make `M.result.if` give the report. Since `match` cannot inspect a computed
    value and recursion cannot be mutual, `drive_good` cannot destructure `STEP(..)`'s pair
    itself; a non-recursive `step_ok` takes the pair as an argument and builds the next `OkR`.
  - The premise `P.Fasta.plain` is unused: the driver definition answers from `B.Fasta.parse`.

## Where it got hard (research data)

- Restructuring cost was concentrated where the spec's *data* changed (DSt's new field), not
  where laws moved: 11 of 15 laws moved by renaming only, and the 4 window/var interface
  statements survived as lemmas unchanged except for the answer type.
- Adding a field to a state record touched every lemma that names a state term, even though no
  invariant mentions the field (Good and need ignore it): a pure threading cost, best done by
  script.
- Rewrite direction, once again: `%e : G` with `e : {new == old}` where `old` is in the goal;
  `ask_le` first had `add_one` the wrong way round (the error shows `G` with `_ := old`).
- Parameter order in matches: `nv.bases` first matched `rr aa` and then `eok` in a branch,
  refused; matching `eok rr aa` together fixed it.
- main.bend: a `+ans` pattern variable inside a nested pair pattern failed elaboration
  ("cannot infer" on `Pair`); a plain `ans` works.
- Process: the lead's commit `2aa2404` swept in my working tree mid-migration (including an
  intermediate alias `WD` that clashed by name with the sim proof's `def WD`), and a
  `git checkout` of one file then restored that intermediate state rather than the original;
  rerunning the scripts on it duplicated two imports. Cheap to fix, but worth knowing: commit
  only files an agent is not working on, or wait for its report.
- Concurrent spec edits: while I worked, `protocol.bend` (`Fasta.plain` redefined over the contigs
  `B.Fasta.parse` keeps) and a comment in `MACHINE.bend` changed in the working tree (not by me,
  uncommitted). The final `./check.sh` passes with them: the machine proof never unfolds the
  premise `hf`, so any definition of `Fasta.plain` checks.
