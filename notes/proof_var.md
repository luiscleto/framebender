# proof_var: notes (agent prove-var)

## Status

Proven (bend --check-only): same_change, stays_valid, standard_form, normal_unchanged, twice,
one_form, shortest. Open: var_in_sound, var_in_enough (in progress, plan below).

## Files

- `proof_var_lists.bend`: list lemmas (append/take/drop/last/init, cancellation, "two cuts of one
  list", Bases/Alleles equality reflection, small Nat order facts).
- `proof_var_rep.bend`: a valid variant as a cut `seq = A ++ REF ++ B` (`A` = the pos-1 bases
  before it); its haps are `A ++ alt ++ B` (`hmap`); validity piece by piece; a cut making the same
  change as a valid variant is valid (distinctness carried through the cut).
- `proof_var_steps.bend`: each normalizer step (trim last base, shift one left, trim first base)
  keeps the change, and the converses (on cuts).
- `proof_var_spec.bend`: the same on whole variants (validity and haps kept), and the spec's tests
  read back: drop_last / drop_first / shift-by-1 keep the change iff all alleles end / start alike.
- `proof_var_n1.bend`: a shift by any k (1 <= k <= pos-1) that keeps the change forces all alleles
  to end alike; hence "not all end alike" makes `movable` false.
- `proof_var_code.bend`: the two loops (`right_ok`, `left_ok`, one Bool invariant each, induction on
  fuel) and `main`: for valid v, `var_in(0, seq, v)` is `Some w` with w valid, same haps, size <= v,
  normalized.
- `proof_var_uniq.bend`: uniqueness (`uniq`).
- `proof_var.bend`: the laws. normal_unchanged = uniq(Norm.var v, v); twice = normal_unchanged on
  Norm.var v; one_form = uniq(Norm.var v, Norm.var w); shortest = one_form + "no bigger".

## Plan

1. Code: the right loop and the left loop keep "valid, same haps, size <= start" (one Bool
   invariant per loop, induction on fuel); the right loop stops with "not all alleles end alike, or
   pos = 1 and some allele has one base"; the left loop keeps that and stops with "not all alike at
   the start, or some allele has one base". From that the output is normalized:
   - left_aligned: a shift by k that keeps the change forces every allele to end like REF
     (last of `C` where `drop(seq, y-k) = C ++ B`), so "not all end alike" rules out every k;
   - parsimonious: drop_last / drop_first keep the change only if all end / start alike.
2. Uniqueness (spec only): two valid normalized variants with the same haps are equal. Cut both
   (`seq = P ++ B = P' ++ B'`, P = A ++ REF): if one cut ends earlier, the other's alleles all end
   alike, so it is at position 1 (left-aligned) and has a one-base allele (parsimonious), but it
   contains the first variant's window plus a base: contradiction. Same ends and different starts:
   the earlier one's alleles all start alike and are long: not parsimonious. Same cut: equal.
3. Laws: normal_unchanged, twice, one_form from uniqueness; shortest from one_form plus "the code
   never grows a variant"; var_in_sound / var_in_enough by simulating the loop on the window.

## Where it got hard

- Rewrite direction: `%e : G` with e : {new == old}; most lemmas are stated "long == short", so
  rewriting long into short needs the reversed lemma (`*_r` in proof_var_lists.bend).
- Equation hypotheses used twice need `+`.
- Recursive defs do not unfold on variables: `V.inits` vs `L.inits` (same body) needed a lemma.
