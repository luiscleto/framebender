# proof_var: notes (agent prove-var)

## Status

**Complete.** All nine laws of the var area are proven in `proof_var.bend` (statements unchanged,
only `+` as given): same_change, stays_valid, standard_form, normal_unchanged, twice, one_form,
shortest, var_in_sound, var_in_enough.

- `bend proof_var.bend --check-only`: 15 TODOs, all of them the other areas' open laws in LAWS.bend
  (it was 24 = 15 + these 9 before).
- Lean kernel: on a scratch copy of the tree whose LAWS.bend keeps only the seven var laws, with a
  PROOF.bend forwarding them to `proof_var.bend`, `bend PROOF.bend --verdict` prints ALL PROOFS CHECK
  (that also covers var_in_sound / var_in_enough, which live in proof_var.bend).
- No code change: `norm_var.bend` is untouched. examples.bend still passes.
- Forwarding for PROOF.bend: `def L.same_change(seq, v, hv): PV.same_change(seq, v, hv)` and so on
  (one_form / shortest take `seq, v, w, hv, hw, hs`; normal_unchanged `seq, v, hv, hn`).
  The window area can call `PV.var_in_sound` / `PV.var_in_enough`.

## Files (about 3200 lines)

- `proof_var_lists.bend`: list lemmas (append/take/drop/get/last/init, left and right cancellation,
  "two cuts of one list" (`cuts`), Bases/Alleles equality reflection), Bool and Nat order facts.
- `proof_var_rep.bend`: a valid variant as a cut `seq = A ++ REF ++ B` (A = the pos-1 bases before
  it); its haps are `A ++ alt ++ B` (`hmap`); validity piece by piece; a cut making the same change
  as a valid variant is valid (distinctness carried through the cut: `A ++ x ++ B` is injective).
- `proof_var_steps.bend`: each step (trim last base, shift one left, trim first base) keeps the
  change, on cuts; and the converses.
- `proof_var_spec.bend`: the same on whole variants; the spec's tests read back: drop_last /
  drop_first / shift-by-1 keep the change iff all alleles end / start alike.
- `proof_var_n1.bend`: a shift by any k (1 <= k <= pos-1) that keeps the change forces all alleles
  to end like REF; so when they do not, `movable` is false.
- `proof_var_code.bend`: the code. `right_ok` / `left_ok` (one Bool invariant each, induction on
  fuel) and `main`: for valid v, `var_in(0, seq, v)` is `Some w`, w valid, same haps, size <= v,
  normalized.
- `proof_var_uniq.bend`: `uniq`: two valid normalized variants with the same haps are equal.
- `proof_var_win.bend`: the window simulation for var_in_sound / var_in_enough.
- `proof_var.bend`: the laws.

## How the laws are proven

- same_change, stays_valid, standard_form: read off `main`.
- normal_unchanged = uniq(Norm.var v, v); twice = normal_unchanged on Norm.var v;
  one_form = uniq(Norm.var v, Norm.var w); shortest = one_form + "the code never grows a variant"
  (size(Norm.var w) <= size(w)). So shortest needed no length arithmetic about the normal form.
- Code loops: the right loop keeps "valid, same haps, size <= start" and stops with "not all alleles
  end alike, or pos = 1 and some allele has one base"; fuel = pos + total suffices (trim lowers the
  total, shift lowers pos; fuel 0 contradicts pos >= 1). The left loop keeps that stop condition
  (trimming the front of long alleles keeps their last bases) and stops with "not all start alike,
  or some allele short". Then normalized: left_aligned by N1 (or pos = 1); parsimonious since
  drop_last / drop_first keep the change only if all end / start alike.
- uniq: cut both variants, `seq = (A ++ REF) ++ B = (A2 ++ REF2) ++ B2`, and compare the cuts with
  `cuts` (no index arithmetic). One window ends later: its alleles all end alike, so it is at
  position 1 (else shift-by-1 keeps the change) and has a one-base allele (else drop_last does),
  but it holds the other window plus a base: contradiction. Same end, one starts earlier: its
  alleles all start alike and are long, so drop_first keeps the change: not parsimonious. Same cut:
  equal (pos from len A, alts by injectivity of `A ++ _ ++ B`).
- var_in_sound: run the window loop and the whole-contig loop side by side (`sim_sound`): a base
  the window returns is the contig's base, and a missing base ends the window run with None.
- var_in_enough: the two runs are equal (`sim_eq`) when every read index pos - 2 (taken at each
  shift) is in the window. Upper end: from covers. Lower end: off <= pos_r - 1, pos_r the position
  after the right loop; positions only decrease (`mono_r`), so every read is at >= pos_r - 1. And
  off <= pos_r - 1 follows from covers because the right loop's result is "pos_r = POS, or some
  allele is short" (`right_shape`: after a shift no allele is long again, so no trim), and with a
  short allele the left loop does not move, so the final POS is pos_r.

## Where it got hard (research notes)

- Rewrite direction was the most common error by far: `%e : G` with e : {new == old} turns old
  into new; lemmas are naturally stated "long == short", so simplifying the goal needs the reversed
  form. Added `*_r` lemmas; the "put `_` on the side holding old, then `{==}`" trick avoids many.
- Transforming a hypothesis (not the goal) is `{%e : P; h : T}` with T = P[old] and h : P[new];
  getting e's orientation right for this was a second source of errors.
- `{%e : P; t}` inside an expression needs the closing `: T` annotation; bare constructor/cons
  lets need annotations (`+r = {g <> u : Q.Bs()}`, `+p2 = {1n+pos : Nat}`).
- Quantities: every equation hypothesis used twice needs `+`; a `1n+f` fuel used twice needs
  `1n+(+f)`; pairs (`A & B`) are not Data, so a pair result is recomputed for each projection
  (`Q.fst` / `Q.snd`); a computed pair or Sigma cannot be destructured by a let or match, only
  through a helper def (`u_top`, `u_same`).
- Match ordering: no let before a match (so validity facts are recomputed in each branch of
  `right_ok`); a field cannot be matched after a later binder was matched: in `(m, pr)` m must be
  matched before pr, and with `match xs xs2` only fields of the second list could be matched
  (reordered parameters in `u1_long`).
- Recursive defs do not unfold on variables: `V.inits` / `L.inits`, `V.tails` / `L.tails`,
  `V.all_long` / `L.all_long.go`, `V.total` / `L.total` (identical bodies) each needed a lemma.
  Non-recursive aliases (`Q.Bs()`, `Q.app`, `RP.vA`) unfold freely and cost nothing.
- No mutual recursion: the loop proofs take the code's Bool tests as parameters with equations
  (`eq == lasts_eq(..)`), so one def matches and recurses; a "for each element" step over a Bool
  list predicate used a closure IH (`short_cons`).
- `Nat.sub(1n+x, 1n)` reduces to `Nat.sub(x, 0n)`, not x: kept positions as `Nat.sub(pos, 1n)`
  opaque and related them to list lengths (`len(A) == pos - 1`) instead of matching on pos.
- Avoiding arithmetic paid off: list cuts (`cuts`, cancellation, last of an append) instead of
  index reasoning for uniqueness and N1; the only real Nat arithmetic is in N1's index bound, the
  window bounds and fuel.
- The lead's closed-form analysis (P, Q, D) was not needed: the proof works from local step
  lemmas plus the "cuts" case split; uniqueness is about two arbitrary normalized variants, not
  about the code.
