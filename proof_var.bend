import Base
import ./types.bend as B
import ./tan.bend as V
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q
import ./proof_var_rep.bend as RP
import ./proof_var_spec.bend as SP
import ./proof_var_code.bend as C
import ./proof_var_uniq.bend as U
import ./proof_var_win.bend as W

# Proofs: the normal form of one variant (Tan.normal, tan.bend).
# Each law below restates the law of the same name in LAWS.bend with every
# variable reusable (+); PROOF.bend forwards L.name to it.

# What the normalizer's answer satisfies (proof_var_code.bend: C.main), read
# back through Maybe.default.

def ext_valid(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, B.Var>, +v: B.Var, +e: {C.good_f(seq, h, s, m) == True{} : Bool}) ->
  {L.valid(seq, Maybe.default(&2, B.Var, m, v)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({L.valid(seq, v) == True{} : Bool}, P.false_ne_true(e))
    case Some{w}:
      match w:
        case B.Var{+p, +r, +xs}:
          C.gd_valid(seq, h, s, p, r, xs, P.and_true_l(C.Gd(seq, h, s, p, r, xs), L.normalized(seq, B.Var{p, r, xs}), e))

def ext_haps(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, B.Var>, +v: B.Var, +e: {C.good_f(seq, h, s, m) == True{} : Bool}) ->
  {L.haps(seq, Maybe.default(&2, B.Var, m, v)) == h : Q.Als()}:
  match m:
    case None{}:
      Empty.absurd({L.haps(seq, v) == h : Q.Als()}, P.false_ne_true(e))
    case Some{w}:
      match w:
        case B.Var{+p, +r, +xs}:
          C.gd_haps(seq, h, s, p, r, xs, P.and_true_l(C.Gd(seq, h, s, p, r, xs), L.normalized(seq, B.Var{p, r, xs}), e))

def ext_size(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, B.Var>, +v: B.Var, +e: {C.good_f(seq, h, s, m) == True{} : Bool}) ->
  {Nat.is_le(L.size(Maybe.default(&2, B.Var, m, v)), s) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Nat.is_le(L.size(v), s) == True{} : Bool}, P.false_ne_true(e))
    case Some{w}:
      match w:
        case B.Var{+p, +r, +xs}:
          C.gd_size(seq, h, s, p, r, xs, P.and_true_l(C.Gd(seq, h, s, p, r, xs), L.normalized(seq, B.Var{p, r, xs}), e))

def ext_norm(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, B.Var>, +v: B.Var, +e: {C.good_f(seq, h, s, m) == True{} : Bool}) ->
  {L.normalized(seq, Maybe.default(&2, B.Var, m, v)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({L.normalized(seq, v) == True{} : Bool}, P.false_ne_true(e))
    case Some{w}:
      match w:
        case B.Var{+p, +r, +xs}:
          P.and_true_r(C.Gd(seq, h, s, p, r, xs), L.normalized(seq, B.Var{p, r, xs}), e)

law same_change:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {L.haps(seq, V.normal(seq, v)) == L.haps(seq, v) : List<&2, List<&2, B.Base>>}

def same_change(seq, v, hv):
  ext_haps(seq, L.haps(seq, v), L.size(v), V.var_in(0n, seq, v), v, C.main(seq, v, hv))

law stays_valid:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {L.valid(seq, V.normal(seq, v)) == True{} : Bool}

def stays_valid(seq, v, hv):
  ext_valid(seq, L.haps(seq, v), L.size(v), V.var_in(0n, seq, v), v, C.main(seq, v, hv))

law standard_form:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {L.normalized(seq, V.normal(seq, v)) == True{} : Bool}

def standard_form(seq, v, hv):
  ext_norm(seq, L.haps(seq, v), L.size(v), V.var_in(0n, seq, v), v, C.main(seq, v, hv))

law normal_unchanged:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hn: {L.normalized(seq, v) == True{} : Bool}
  {V.normal(seq, v) == v : B.Var}

def normal_unchanged(seq, v, hv, hn):
  U.uniq(seq, V.normal(seq, v), v, stays_valid(seq, v, hv), hv, standard_form(seq, v, hv), hn, same_change(seq, v, hv))

law twice:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  {V.normal(seq, V.normal(seq, v)) == V.normal(seq, v) : B.Var}

def twice(seq, v, hv):
  normal_unchanged(seq, V.normal(seq, v), stays_valid(seq, v, hv), standard_form(seq, v, hv))

law one_form:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +w: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hw: {L.valid(seq, w) == True{} : Bool}
  for +hs: {L.haps(seq, v) == L.haps(seq, w) : List<&2, List<&2, B.Base>>}
  {V.normal(seq, v) == V.normal(seq, w) : B.Var}

def one_form(seq, v, w, hv, hw, hs):
  U.uniq(seq, V.normal(seq, v), V.normal(seq, w), stays_valid(seq, v, hv), stays_valid(seq, w, hw),
    standard_form(seq, v, hv), standard_form(seq, w, hw),
    SP.trans3(L.haps(seq, V.normal(seq, v)), L.haps(seq, v), L.haps(seq, w), L.haps(seq, V.normal(seq, w)),
      same_change(seq, v, hv), hs, same_change(seq, w, hw)))

law shortest:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +w: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hw: {L.valid(seq, w) == True{} : Bool}
  for +hs: {L.haps(seq, v) == L.haps(seq, w) : List<&2, List<&2, B.Base>>}
  {Nat.is_le(L.size(V.normal(seq, v)), L.size(w)) == True{} : Bool}

def shortest(seq, v, w, hv, hw, hs):
  %Equal.sym(B.Var, V.normal(seq, v), V.normal(seq, w), one_form(seq, v, w, hv, hw, hs)) :
    {Nat.is_le(L.size(_), L.size(w)) == True{} : Bool}
  ext_size(seq, L.haps(seq, w), L.size(w), V.var_in(0n, seq, w), w, C.main(seq, w, hw))

law unique:
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +w: B.Var
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hw: {L.valid(seq, w) == True{} : Bool}
  for +hnv: {L.normalized(seq, v) == True{} : Bool}
  for +hnw: {L.normalized(seq, w) == True{} : Bool}
  for +hs: {L.haps(seq, v) == L.haps(seq, w) : List<&2, List<&2, B.Base>>}
  {v == w : B.Var}

def unique(seq, v, w, hv, hw, hnv, hnw, hs):
  U.uniq(seq, v, w, hv, hw, hnv, hnw, hs)

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
  {w == V.normal(seq, v) : B.Var}

def var_in_sound(seq, off, bases, v, w, hb, hv, hw):
  match v:
    case B.Var{+pos, +ref, +alts}:
      +als = {ref <> alts : Q.Als()}
      +fu = Nat.add(pos, V.total(als))
      +rw = V.right(fu, V.next_act(off, bases, pos, als), off, bases, pos, als)
      +rs = V.right(fu, V.next_act(0n, seq, pos, als), 0n, seq, pos, als)
      +hs = W.lo(rw, rs, w,
        c => e => W.sim_sound(fu, V.lasts_eq(als), V.all_long(als), Nat.is_le(2n, pos), V.Win.get(off, bases, Nat.sub(pos, 2n)),
          V.Win.get(0n, seq, Nat.sub(pos, 2n)), off, bases, seq, pos, als, c, hb, {==}, {==}, e), hw)
      %Equal.sym(Maybe<&2, B.Var>, V.left_of(rs), Some{w}, hs) : {w == Maybe.default(&2, B.Var, _, B.Var{pos, ref, alts}) : B.Var}
      {==}

# A window holding what the normalization reads gives an answer.
law var_in_enough:
  for +seq: List<&2, B.Base>
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +v: B.Var
  for +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>}
  for +hv: {L.valid(seq, v) == True{} : Bool}
  for +hc: {covers(off, L.len(bases), v, V.normal(seq, v)) == True{} : Bool}
  {Maybe.is_some(&2, B.Var, V.var_in(off, bases, v)) == True{} : Bool}

def var_in_enough(seq, off, bases, v, hb, hv, hc):
  match v:
    case B.Var{+pos, +ref, +alts}:
      +v0 = {B.Var{pos, ref, alts} : B.Var}
      +als = {ref <> alts : Q.Als()}
      +fu = Nat.add(pos, V.total(als))
      +rw = V.right(fu, V.next_act(off, bases, pos, als), off, bases, pos, als)
      +rs = V.right(fu, V.next_act(0n, seq, pos, als), 0n, seq, pos, als)
      +hsl = W.gf_some(seq, L.haps(seq, v0), L.size(v0), V.left_of(rs), C.main(seq, v0, hv))
      +hsh = W.right_shape(fu, V.lasts_eq(als), V.all_long(als), Nat.is_le(2n, pos), V.Win.get(0n, seq, Nat.sub(pos, 2n)), 0n, seq, pos, als, pos,
        {==}, Q.or_tt_l(Nat.is_eq(pos, pos), Bool.not(V.all_long(als)), P.eq_refl(pos)))
      +c1 = Nat.is_le(off, Nat.min(Nat.sub(pos, 1n), Nat.sub(L.pos_of(V.normal(seq, v0)), 2n)))
      +c2 = Nat.is_le(Nat.add(Nat.sub(pos, 1n), L.len(ref)), Nat.add(off, L.len(bases)))
      +hlo = W.hlo_of(rs, off, pos, v0, W.lo_some(rs, hsl), hsh, P.and_true_l(c1, c2, hc))
      +hup = W.hup_of(pos, L.len(ref), Nat.add(off, L.len(bases)), RP.vk1(seq, pos, ref, alts, hv), RP.vk2(seq, pos, ref, alts, hv),
        P.and_true_r(c1, c2, hc))
      +heq = W.sim_eq(fu, V.lasts_eq(als), V.all_long(als), Nat.is_le(2n, pos), V.Win.get(off, bases, Nat.sub(pos, 2n)),
        V.Win.get(0n, seq, Nat.sub(pos, 2n)), off, bases, seq, pos, als, hb, {==}, {==}, {==}, hlo, hup)
      %Equal.sym(Maybe<&2, V.Cur>, rw, rs, heq) : {Maybe.is_some(&2, B.Var, V.left_of(_)) == True{} : Bool}
      hsl
