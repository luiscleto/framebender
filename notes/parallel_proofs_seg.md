# Phase E, area B (seg): the segment lemma

## Status (2026-10-28): DONE

`seg` in `proof_e_seg.bend` is proven; its statement is unchanged (one import added,
`proof_e_seg_main.bend as SM`, and the `?TODO` filled). No counterexample: segok is strong
enough. No TODO of mine is left.

- `timeout 1800 test/bcheck.sh proof_e_seg.bend --check-only` prints "13 TODOs found": all 13
  are LAWS.bend's open laws (a file importing only LAWS.bend reports the same 13; before the fill
  it reported 14). Every helper file below reports only those 13.
- `--verdict` on the real file stops at those 13 before the kernel runs (as in area C). A scratch
  copy of framebender's and `../lawful-*`'s `.bend` files with LAWS.bend's 13 open laws removed
  (nothing here uses them): `test/bcheck.sh <copy>/proof_e_seg.bend --check-only` and
  `--verdict` both print **ALL PROOFS CHECK**.
- In fact the true run equals `shiftS` exactly (`SM.segx`); `seg` applies `P.settle` to both sides.

| file | what |
|---|---|
| `proof_e_seg_defs.bend` | lift, img, allreal, qok, inv2, M, Good, G1, Good1, Bad, all_lt, fmap |
| `proof_e_seg_lem.bend` | moving items on by d commutes with insert, take/drop_ready, flush (`fl2`); allreal, keys_ge, all_lt kept; counts |
| `proof_e_seg_lem2.bend` | E in front of T's buffer (ready or not as a whole), `flush_app`, last items, Nat facts, `good1_notbad` |
| `proof_e_seg_mono.bend` | `good_back` (T's good end state: every earlier state good), `doom` (the backward fact) |
| `proof_e_seg_par.bend` | phase 2: `par` (X = lift(Y) along the rest) |
| `proof_e_seg_drain.bend` | phase 1: `drain` (S's buffer E not all written yet) |
| `proof_e_seg_top.bend` | `ib_go` (a run in the body stays there), key bounds, `sorted_conv`, `img_ls`, `first` (the first line when S's CHROM is not c0) |
| `proof_e_seg_main.bend` | `segx`: the three cases and `fin` (lift of T's end is shiftS) |

## The proof

X: the true run from S; Y: T's run from `rs0(c0, l)`, on the same lines.

- **Phase 2** (E all written): X = `lift(Y)`: lines `+ S.n`, S's head, ended `Y's ++ z`, out
  `p ++ Y's`, counts added, S's notes (Y has none), buffer moved on by S.n, last item
  `img(q, Y's)`: the phantom stands for q (`qok`: q's key at most the phantom's), a real item for
  itself. Y's flush passing implies X's (`fl2`). New CHROMs: `has(chrom, z)` is false (`zfree`,
  from chroms_ok via `nr_cond`); z is S's ended list (same CHROM) or it with S's CHROM pushed.
- **Phase 1** (same CHROM, E not empty): X's buffer is `E' ++ shift(Y's)`, Y's last is the
  phantom, Y wrote nothing, X's written text and last are tracked by `Px ++ texts(E') = P0` and
  `Maybe.or(last(E'), q) = Q0`. Each line: a key below l: `doom` (T stops, or keeps the key to
  the end, which segok's keys_ge refuses). Else if all of E' is ready, X writes E' then exactly
  Y's writes (hand-off to phase 2 with q = Q0); else X writes a prefix of E' and Y nothing (Y's
  head key is at least l, at least E's max, so not ready), and every Y item has input POS below
  max(E) + w. At the end E' cannot be left: segok's `mlow` says some item reaches max(E) + w.
- **New CHROM** (S's is not c0): the first line writes all of S's buffer and both runs start c0
  (`first`), then phase 2 with q = None.
- `good_back`: T's end state not stopped, without messages, with fresh CHROMs implies the same of
  every state before it, so each step's bad branches (a stop, a message) are refuted.

## What was hard (research data)

- **Rewrite direction.** `%e : P` with `e : {a == b}` replaces b (marked `_` in P) by a. Most of
  my failed checks were the wrong direction; marking `_` on the other side of the goal often
  avoids an `Equal.sym`.
- **Match order.** A parameter cannot be matched after a later one (`match sc sb same` jointly,
  `match i ns x` in declaration order), and a computed pair cannot be destructured: pass it to
  a helper that takes it as a parameter and matches it.
- **No erased hypotheses in proofs.** A function hypothesis (`@x -> ... -> {has(x, z) == False}`)
  is Type, so it cannot be reused across the induction, and `-` hypotheses cannot be used in a
  proof. Replaced by Data equations and a lemma (`zfree`).
- **No mutual recursion**: induction hypotheses go to helpers as lambdas (`DoomIH`, `DrainIH`).
- **Pairs as goals** (`{eq} & {inv}`) can be rewritten with `%`; this kept the step lemmas to one
  case analysis each.
- **Generated text.** The state terms are long; a Python generator (scratchpad) wrote the
  statements and rewrite motives, which kept them consistent.
- Early on I ran `bend` directly about ten times for short probes and error headers (bcheck.sh
  prints only the last 40 lines); everything since went through bcheck.sh.
