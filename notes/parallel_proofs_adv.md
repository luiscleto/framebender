# Phase E, area A (adv-moved): AdvG gives the state-level step

## Status (2026-10-28)

DONE. `PROOF.bend` passes `test/bcheck.sh --check-only` (23 s) and `--verdict` (40 s).

- `proof_b_simdefs.bend`: `S.Moved` and AdvG's two new clauses:
  - Went, Want and Idle end with
    `({guard(O, N, p2) == True{} : Bool} & ({StP.o(p2) == StP.o(p) : B.Opts} & Moved(fa, cs, p, p2)))`;
  - Ended and Yield end with `({guard(O, N, p2) == True{} : Bool} & {StP.o(p2) == StP.o(p) : B.Opts})`.
- One deviation from the text in notes/parallel_proofs.md: Bend refuses `match StP.md(p) StP.md(p2)`
  ("a match cannot scrutinize a computed value"). So `Moved` is a one-line def calling
  `Moved.md(StP.md(p), StP.md(p2), fa, cs, p, p2)`, and `Moved.md` does the match. The two
  cases are the design's, word for word (the same split as `report` / `report.md`). On a
  concrete p and p2, `S.Moved(fa, cs, p, p2)` reduces to the case. On abstract ones it stays
  `S.Moved.md(S.StP.md(p), S.StP.md(p2), ...)`: match on p to open it.
- Producers:
  - `proof_b_adv_line.bend`'s `moved_line` (used by `went_line`, so every line path: fast,
    slow, hit, the header paths, the #CHROM line): `ls = [line]`. The lines come from `itx` and
    `hlc` (the same chain as `rep_line`), and the run part is `hrun`, since
    `run.go([l], st) = line_step(st, l)`.
  - `proof_b_adv_wf.bend`'s `moved_keep(fa, cs, rp, p, q, eqi)`: `ls = []` for a step that keeps
    the run, with `eqi : intext(q) == intext(p)`. It covers the buffer end (`part.len`'s `DP.e` /
    `DP.nn`, with the existing `eqi`), the byte-mode Wants (slow `SL.vw`, fast `F.wt`: `{==}`) and
    the byte-mode Idle (`proof_b_adv.bend`'s `mbsrc`: `{==}`).
  - `proof_b_adv_ms.bend`'s `moved_msO`: a step into the String mode (`to_ms_went`) gives
    `Unit{}`. It is a lemma because `msO` is stuck on an abstract run.
  - Steps from the String mode give `Unit{}` directly: `Moved.md(MSP{..}, _)` reduces.
    `W.moved_ms` exists for an abstract second state but is not used yet.
  - The options clause is `{==}` everywhere.
- Consumers: `proof_b_drive_pump.bend` (`pump_go`) and `proof_b_budget_step.bend` (`pb_go`)
  take apart the extra components and ignore them. `proof_b_budget_fast.bend` uses its own
  AdvC and needed no change.

## Using Moved (for areas B to E)

From `S.AdvG(fa, T, cs, O, N, p, Norm.Went{st})`, the last component of the tuple is
`S.Moved(fa, cs, p, p2)`. With p and p2 in the byte mode, opened by matching on their `md`, it is
`(ls, (hlines, hrun))`, where
`hlines : lines(intext(p, cs)) == ls ++ lines(intext(p2, cs))` and
`hrun : settle(specRun(rp2)) == settle(L.run.go(ls, fa, StP.o(p), specRun(rp)))`.

## What was hard

- The design's Moved did not parse as written (see above).
- Keeping shared files parseable: other agents' checks import the adv chain through
  `proof_b_sim.bend`, and a missing paren in `proof_b_adv_part.bend` broke their checks for a
  moment. From then on every edit went to a scratch copy, `proof_e_a_tmp_<name>.bend` in the
  tree (so relative imports resolve). The copy was checked, then moved over the original only
  when it passed.
- Ended and Yield are built only in `proof_b_adv.bend` (`mb.k`, `msfull`, `ms.k`), so the
  options clause touched few sites.
