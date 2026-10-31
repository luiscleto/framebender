import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_lines.bend as LN
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_line.bend as LI
import ./proof_b_alleles_loop.bend as ALP
import ./proof_s_line.bend as SL
import ./proof_s_multi.bend as MU
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_list.bend as BL
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# The fast path with -m (norm_seq.bend's body.m): a line reaches it only
# when NS.multi finds no comma in its ALT field (or without -m), and then
# B.Rec.parts leaves the line whole (proof_s_multi.bend). Every variable is
# reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def X(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

def unsome(m: Maybe<&2, U32>) -> U32:
  Maybe.default(&2, U32, m, 0)

# The first LF from at, below len, is at lf.
def lf_byte(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +at: U32, +lf: U32,
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hfl: {D.first(X(len, t), n(at), n(len), 10) == n(lf) : Nat},
  +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) -> {C.AT(len, t, lf) == 10 : U32}:
  +V = X(len, t)
  +hg = ALP.has_get(V, n(lf), 10,
    %Equal.sym(Nat, n(lf), D.first(V, n(at), n(len), 10), Equal.sym(Nat, D.first(V, n(at), n(len), 10), n(lf), hfl)) : {D.has(V, _, 10) == True{} : Bool};
    BL.first_hit(V, n(at), n(len), 10, LI.u2n(at, len, hs), %LP.len_x(len, t, d, hok) : {Nat.is_le(n(len), _) == True{} : Bool}; N.le_refl(n(len)),
      %Equal.sym(Nat, D.first(V, n(at), n(len), 10), n(lf), hfl) : {Nat.is_lt(_, n(len)) == True{} : Bool}; hlt))
  +ha = C.at_view_t(len, t, d, lf, C.ok_full(len, t, d, hok), C.ok_d(len, t, d, hok), C.ok_len(len, t, d, hok), hlt)
  Equal.cong(Maybe<&2, U32>, U32, unsome, Some{C.AT(len, t, lf)}, Some{10},
    Equal.trans(Maybe<&2, U32>, Some{C.AT(len, t, lf)}, List.get(&2, U32, V, n(lf)), Some{10}, ha, hg))

# The fast path's line at .. lf (its first LF): whole when the test passed.
law hw_line:
  for +dfs: B.Defs
  for +o: B.Opts
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +at: U32
  for +lf: U32
  for +hs: {U32.is_le(at, len) == True{} : Bool}
  for +hfl: {D.first(X(len, t), n(at), n(len), 10) == n(lf) : Nat}
  for +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool}
  for +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  for +hmw: {MU.MW(o, len, t, at) == True{} : Bool}
  {B.Rec.parts(dfs, o, B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == B.Whole{} : B.Parts}

def hw_line(dfs, o, len, t, d, hok, at, lf, hs, hfl, hal, hlt, hmw):
  +A = SL.TXR(len, t, at, lf)
  %Equal.sym(B.Line, Norm.line(A), B.Text.line(A), LN.line_eq(A)) :
    {B.Rec.parts(dfs, o, B.Line.body(_)) == B.Whole{} : B.Parts}
  %Equal.sym(B.Line, B.Text.line(A), SL.LINE(len, t, at, lf, SL.BE(len, t, at, lf)), SL.line_t(len, t, d, hok, at, lf, hal, hlt, lf_byte(len, t, d, hok, at, lf, hs, hfl, hlt))) :
    {B.Rec.parts(dfs, o, B.Line.body(_)) == B.Whole{} : B.Parts}
  MU.mw_whole(len, t, d, hok, dfs, o, at, lf, hal, hlt, Equal.sym(Nat, D.first(X(len, t), n(at), n(len), 10), n(lf), hfl), hmw)
