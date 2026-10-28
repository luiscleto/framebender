# Phase B, area "cut": status and notes

Brief: `notes/briefs/BYTES_PROOFS_CUT.md`. Deliverables: `proof_b_cut.bend`.

## Status

| deliverable | status |
|---|---|
| `line_pair` | proven |
| `pass_lf` | proven |
| `pass_alleles` | proven |
| `line_text` | proven |
| `pass_fields` | proven |
| `pass_pos` | proven |
| `pass_pos_small` (added by the lead) | proven |

The only other TODOs are the 5 holes of `proof_b_fasteq.bend` (on purpose).

Check (only through the capped wrapper): `timeout 1800 test/bcheck.sh proof_b_cut.bend --check-only`.
Checked that way after the rule change, and again under the prlimit (4 GB address space) version: about 2 s, "5 TODOs found" (fasteq's), no "bcheck: bend exited with N".

## Files

- `proof_b_cut_pair.bend`: every call `NF.line` makes on `C.BT(len, t)`
  hands the mirror back, with its answer mirrored on Data. `line_t`:
  `NF.line(BT, s) == Pr{BT, PRE(len, t, s)}`.
  - The cut is mirrored without threading: `E0 .. E7` are functions of `s`
    (`E(i+1) = TJ(E(i) + 1)`), and `c0 .. c8` only carry the two flags of
    each search. The inversion is then a case split per level, with no
    rewriting of threaded values.
  - num, bases, dup, alts, noend: one Data mirror per loop (`NG`, `BGm`,
    `DGm`, `AGm`, `NG2`) and one lemma by induction on the fuel.
- `proof_b_cut_inv.bend`: `inv`: `PRE(len, t, s) == Pass{...}` gives the
  flags of every search (`FI0`), the cut as `E0 .. E7` and the line's LF
  (`ME(...) == K8(e..)`), and the tests passed (`PT`). `dst` hands the
  facts to a continuation one by one.
- `proof_b_cut_nat.bend`: the searches as facts about the view (`FF`: first
  tab or LF, inside the buffer; `tabget`; `nxt`), `unq` (the first c is g
  when g holds c and nothing before it does), and its uses `skip10`, `hit10`,
  `first9`, `lf10`, `lff`.
- `proof_b_cut_fx.bend`: the field facts in E-form (generated lets), the
  core of `pass_lf` (`lf_core`), and the bounds `ltE0 .. ltE7`.
- `proof_b_cut_str.bend`: text facts: `ltext_nl` (Norm.line's text with
  terminator is the text and LF), `fld_nl`, `cut_fld` (J.cut of a field's
  text at its first tab), `body_eq` (Norm.line's body: a final CR cut off).
- `proof_b_cut_ne.bend`, `proof_b_cut_ne2.bend`: INFO's END test.
  `noend_ok`: the bytes loop (`M.NE`) passing gives `J.noend` on INFO's
  text. An induction over INFO's positions walks J.noend.go and the
  E-to-E bytes loop together (`ne_ind`); `e_ne` shows an E whose key test
  failed starts no END entry in the text (case tree over the next 3 bytes).
- `proof_b_cut_pos.bend`: POS. `ng_v`: num's loop computes the digits'
  value, with each step's accumulator bounded by a word constant `PK(J)`
  (9, 99, ...) and lawful-fields' `FITSU`/`ena` for the no-overflow facts
  (2^32 abstract as M). `show_snoc`/`go_fuel`: Nat.show(10q + r) is
  Nat.show(q) then r's digit. `pos_core`, `pos_small`.

## Where it got hard (research data)

- Rewrite direction, as always: about one slip in five rewrites, each fixed
  from the expected/observed message.
- A pair of equalities is a Type, not Data, so a fact bundle can't be a `+`
  parameter or a `+` let. Fix: projection lemmas (`ff1`, `ff2`, ...) that
  take the bundle as their only use, called once per component on a fresh
  copy of the producing lemma.
- `+x` inside a nested tuple pattern (`case (a, (b, +c))`) failed with
  "cannot infer"; one-level matches work.
- A rewrite inside a tuple component (`(x, (%e : P; y))`) can't be
  inferred; move it into its own def, or use `AB.subst` as an expression.
- `match` after a let is refused: the lemma that matches takes the
  computed facts as parameters from a wrapper that has the lets.
- Type-valued lets (`+R = NF.B4{...}`) are refused: name them as defs.
- The checker is fast here (under 2 s per file): the mirrors keep every
  term small, and no big Nat is ever normalized.
- **2^32 in context breaks error messages.** With `hm: {Nat.pow(2n, 32n) ==
  M}` in scope, any type error (even a missing annotation) crashed the
  error printer with "Maximum call stack size exceeded", which looks like
  the 2^32 trap but is not. Debugging: restate the failing step in a def
  without `hm`, which prints the real error. Three such masked errors: a
  name that does not exist (`N.le_add`), a bare literal let (`+D9 = 9n`),
  and a `+` let of a tuple.
- Conversions between two different `U32.to_nat(...)` terms are risky;
  every bound was kept as a U32 fact (`PK(J)`, `U32.is_lt(pos,
  1000000000)`), and word identities such as `PK(1+J) == NA(PK(J), 57)`
  are checked at word level.
- Fuel: Bend's `Nat.show` uses the number itself as fuel; `go_fuel` (any
  fuel above the number gives the same text) was needed for
  `show(10q + r)`.
- Termination: the first argument that changes must shrink, so `valn`
  takes the list first.
- Size: about 4200 lines over 10 files; each check runs in under 2 s.
  Most of the bulk is the generated per-field code (8 fields of lets) and
  the case trees of the END test.

## Statements

All seven statements are true as stated and usable; nothing to report.

## Follow-up (2026-10-28, by the lines agent): `--verdict` past 4 GB, fixed

`bend proof_b_cut.bend --verdict` now passes (about 17 s). Before, the kernel recheck went over the 4 GB cap in
`proof_b_cut_fx.bend`. This only showed once fasteq's holes were filled: until then `--verdict` refused to run
at all.

- **Cause:** `lf_q`'s result type is `LFG(len, t, s, V.LFm(len, t, s, q))`, while each branch's proof is about
  `M.E7(len, t, s)` (q False) or `M.LF1(len, t, s)` (q True).
  - bend's checker accepts `V.LFm(.., False) ≡ M.E7(..)` without trouble. The kernel apparently does not: it
    seems to normalize the whole 11-part result type to compare it.
  - That unfolds `E7`. `E7` is eight nested `TJ` searches (each `E_i` starts at `E_{i-1} + 1`), and each is the
    word-at-a-time `find2`, so the term grows past 4 GB.
  - Evidence: each half of a branch passes `--verdict` in ~5 s on its own (the `D.first` chain with `M.E7`
    written out, and the tuple of bounds). The same branch with `M.E7` written into the result type also passes.
- **Fix** (in `proof_b_cut_fx.bend` only):
  - `lf_q`'s two branches are now separate lemmas, `lf_qF` (result `LFG(.., M.E7(..))`) and `lf_qT` (result
    `LFG(.., M.LF1(..))`). `lf_qT` takes `hl` in the form `Z.lff` uses (`U32.is_eq(M.LJ(.., E7 + 1), len) ==
    False`).
  - `lf_q` keeps its statement. It dispatches on `q` and reaches `V.LFm`/`V.LPm` through `AB.subst` with
    small `{==}` equations (`M.E7 == V.LFm(.., False)`, `M.LF1 == V.LFm(.., True)`, `V.LPm(.., True) ==
    U32.is_eq(M.LJ(..), len)`). The kernel accepts each in a few seconds.
  - No deliverable statement changed.
- **Lesson:** in a `--verdict` proof, write a computed index (a field end found by searches) in the same form
  in the type and in the proof term. A one-step definitional rewrite (`LFm(.., False)` to `E7`) is cheap for the
  checker but not for the kernel, when the term behind it is big.
