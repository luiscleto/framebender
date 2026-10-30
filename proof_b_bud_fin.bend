import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import lawful-words@0.1.0.0/proof_nat.bend as N

# The budget's Finish cases (bud_chunk_fin, bud_eof_fin, bud_ref_fin of
# proof_b_budget_api.bend): a step that ends the run leaves need at least
# 2 + the reads it answers. need (BN.need) is
#   (pieces left + 1 before eof) + (2 + (hand-outs + (RD(nx) + WA))),
# with RD(Ask{rs}) = 1 + |rs|, so this is arithmetic on its shape.

# 2 <= a + (2 + x).
def le2(+a: Nat, +x: Nat) -> {Nat.is_le(Nat.add(0n, 2n), Nat.add(a, Nat.add(2n, x))) == True{} : Bool}:
  N.le_trans(2n, Nat.add(2n, x), Nat.add(a, Nat.add(2n, x)), N.le_add_r(2n, x), N.le_add_l(Nat.add(2n, x), a))

# |rs| + 2 <= a + (2 + (h + ((1 + |rs|) + w))).
def le_rs(+a: Nat, +h: Nat, +lr: Nat, +w: Nat) ->
  {Nat.is_le(Nat.add(lr, 2n), Nat.add(a, Nat.add(2n, Nat.add(h, Nat.add(1n+lr, w))))) == True{} : Bool}:
  +y = Nat.add(h, Nat.add(1n+lr, w))
  +h1 = N.le_trans(lr, Nat.add(lr, w), Nat.add(1n+lr, w), N.le_add_r(lr, w), N.le_add_l(Nat.add(lr, w), 1n))
  +h2 = N.le_trans(lr, Nat.add(1n+lr, w), y, h1, N.le_add_l(Nat.add(1n+lr, w), h))
  +h3 = N.le_trans(Nat.add(2n, lr), Nat.add(2n, y), Nat.add(a, Nat.add(2n, y)), N.le_add_mono_l(2n, lr, y, h2), N.le_add_l(Nat.add(2n, y), a))
  %N.add_comm(2n, lr) : {Nat.is_le(_, Nat.add(a, Nat.add(2n, y))) == True{} : Bool}
  h3

def chunk_fin(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +p: S.StP) ->
  {Nat.is_le(Nat.add(0n, 2n), BN.need(fa, T, p, c <> cs, False{}, Pr.More{}, O)) == True{} : Bool}:
  le2(Nat.add(List.length(&2, String, c <> cs), BN.pick(Bool.not(False{}), 1n)), Nat.add(BN.HO(T, O), Nat.add(BN.RD(Pr.More{}), BN.WAS(fa, S.mkSt(fa, p), c <> cs))))

def eof_fin(+fa: List<&2, B.Contig>, +T: R.Report, +O: String, +p: S.StP) ->
  {Nat.is_le(Nat.add(0n, 2n), BN.need(fa, T, p, Nil{}, False{}, Pr.More{}, O)) == True{} : Bool}:
  le2(Nat.add(List.length(&2, String, Nil{}), BN.pick(Bool.not(False{}), 1n)), Nat.add(BN.HO(T, O), Nat.add(BN.RD(Pr.More{}), BN.WAS(fa, S.mkSt(fa, p), Nil{}))))

def ref_fin(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +de: Bool, +rs: List<&2, Pr.Req>, +O: String, +p: S.StP) ->
  {Nat.is_le(Nat.add(List.length(&2, Pr.Req, rs), 2n), BN.need(fa, T, p, cs, de, Pr.Ask{rs}, O)) == True{} : Bool}:
  le_rs(Nat.add(List.length(&2, String, cs), BN.pick(Bool.not(de), 1n)), BN.HO(T, O), List.length(&2, Pr.Req, rs), BN.WAS(fa, S.mkSt(fa, p), cs))
