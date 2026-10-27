import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./norm_var.bend as V
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P

# Proofs: the normal form of one variant (Norm.var, norm_var.bend).
# Each law below restates the law of the same name in LAWS.bend with every
# variable reusable (+); PROOF.bend forwards L.name to it.

law same_change:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {L.haps(seq, Norm.var(seq, v)) == L.haps(seq, v) : List<&2, List<&2, B.Base>>}

law stays_valid:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {L.valid(seq, Norm.var(seq, v)) == True{} : Bool}

law standard_form:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {L.normalized(seq, Norm.var(seq, v)) == True{} : Bool}

law normal_unchanged:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hn: {L.normalized(seq, v) == True{} : Bool}
  {Norm.var(seq, v) == v : B.Var}

law twice:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {Norm.var(seq, Norm.var(seq, v)) == Norm.var(seq, v) : B.Var}

law one_form:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +w: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hw: {L.valid(seq, w) == True{} : Bool}
  for +hs: {L.haps(seq, v) == L.haps(seq, w) : List<&2, List<&2, B.Base>>}
  {Norm.var(seq, v) == Norm.var(seq, w) : B.Var}

law shortest:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +w: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hw: {L.valid(seq, w) == True{} : Bool}
  for +hs: {L.haps(seq, v) == L.haps(seq, w) : List<&2, List<&2, B.Base>>}
  {Nat.is_le(L.size(Norm.var(seq, v)), L.size(w)) == True{} : Bool}

# ---------------------------------------------------------------------------
# Interface for proof_window.bend: the normalizer reading a window
# ---------------------------------------------------------------------------

def ref_len(v: B.Var) -> Nat:
  match v:
    case B.Var{p, r, a}:
      L.len(r)

# The window holds every base from one before the new POS (or from the input
# POS when that is earlier) to the end of the input REF (0-based indexes).
def covers(+off: Nat, +n: Nat, +v: B.Var, +w: B.Var) -> Bool:
  Nat.is_le(off, Nat.min(Nat.sub(L.pos_of(v), 1n), Nat.sub(L.pos_of(w), 2n)))
    && Nat.is_le(Nat.add(Nat.sub(L.pos_of(v), 1n), ref_len(v)), Nat.add(off, n))

# Any answer the normalizer gives from a window of the contig is the answer
# for the whole contig.
law var_in_sound:
  for +seq: List<&2, B.Base>
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +v: B.Var
  for +w: B.Var
  for +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>}
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hw: {V.var_in(off, bases, v) == Some{w} : Maybe<&2, B.Var>}
  {w == Norm.var(seq, v) : B.Var}

# A window holding what the normalization reads gives an answer.
law var_in_enough:
  for +seq: List<&2, B.Base>
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +v: B.Var
  for +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>}
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hc: {covers(off, L.len(bases), v, Norm.var(seq, v)) == True{} : Bool}
  {Maybe.is_some(&2, B.Var, V.var_in(off, bases, v)) == True{} : Bool}
