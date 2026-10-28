# Phase B, area "frame": notes

## Status (2026-10-27)

All six deliverables in `proof_b_frame.bend` are proven: `settle_inv`, `step_pre`, `run_pre`,
`finish_pre`, `settle_pre`, `run_halted`. None of the file's own `?TODO`s is left. The check
reports the same TODO count as `proof_b_sim.bend` checked alone (40 when last run), so every
TODO it reports is inherited: LAWS.bend's 13 open laws and other areas' holes behind
proof_b_sim. A copy with one proof broken on purpose fails with the error, so the TODO count
does not hide errors. The only change to the skeleton is the removed `?TODO` lines (checked
with diff), plus two imports and a bridge lemma.

Files:
- `proof_b_frame.bend`: the deliverables, and `pre_eq`
  (`F.pre(O, N, st) == S.pre(O, N, st)`, by matching st). Each `pre` deliverable rewrites
  `S.pre` to `F.pre` and calls the helper.
- `proof_b_frame_fr.bend` (imports run.bend, LAWS.bend, proof_base, proof_machine_nat only):
  - `pre`: a copy of S.pre's definition.
  - from `proof_machine_frame.bend` as it was: `rs_eq`, `fr_*` (commute with pre) and
    `ib_*` (keep inbody). Dropped: the projections that used the old `Norm.RunSt.*`.
  - new: `head_pre` (a header line, O empty), `step_pre`, `ib_step`, `hg_go`/`hg_step` (the
    guard survives a line), `run_pre`, `ff_pre`/`nh_pre`/`finish_pre`, and `run_halted` (from
    proof_machine_sim's `run_go_halted`).
- `proof_b_frame_bl.bend` (imports proof_b_defs for `blank`/`blank_st`): a report does not
  read the last item's text (`inv`), proven on run.bend's functions directly.

`settle_inv`: on a running state `settle` is `blank_st`, so `inv` applies. On a stopped state
both runs stay as they are (`run_halted`), and `finish` of a stopped state reads only out and
notes.

## Where it got hard (research data)

- **The old `inv` did not carry over.** proof_fast_run.bend proved it through the old String
  machine's own bookkeeping (`N.flush`, `N.same_run`, ...), which blanked internally, and
  those definitions are gone. The new route compares run.bend with itself, up to `blank_st`
  on both sides:
  - `bF` blanks a flush result's last item. `flush_bl`: `bF(flush(items, blank L)) ==
    bF(flush(items, L))`. For a non-empty list the two are even equal, since `flush.put`
    reads last only for `flush.ok` and `at_of`, and blank keeps both.
  - Two pieces per consumer of a flush result: `emit_bF`/`ng_bF` (the result's last is not
    read, or only up to blank) and `emit_st`/`ng_st` (the state's last is not read, or is
    replaced). `emit_both` and `new_run_bl` chain them.
  - The rest (`keyed`, `problem_line`, `body_line`, `head_line`, `step`, `finish`, `inv`)
    follows the old file's shape.
- **Stuck matches on a field.** `R.finish` matches `inbody` and `halt` together, so with
  `inbody` a variable even a stopped state's finish does not reduce. The stopped case of
  `settle_inv` is split on `inbody` (two identical bodies).
- **Two definitions of pre.** The helpers keep a copy of `S.pre` so they do not depend on
  proof_b_sim, which has other areas' holes and changes under them. A three-line bridge
  lemma, plus two rewrites per deliverable, connects them: `F.pre(st)` and `S.pre(st)` are
  not convertible while st is a variable.
- **The guard in `run_pre`.** `inbody || (O empty && N empty)` has to hold after every line.
  `hg_go` takes inbody as a Bool c with `hc : inbody(st) == c`. When it is True, `ib_step`
  keeps it True; when False, the right side was True already.
- **Imported TODOs.** Any file that imports LAWS.bend reports its 13 laws as TODOs. To check
  a helper, compare its count with LAWS.bend's alone. To make sure errors are not hidden
  behind the TODO count, break a proof on purpose once.
