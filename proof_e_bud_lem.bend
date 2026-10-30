import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_budget_need.bend as BN
import ./proof_base.bend as PB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_b_simdefs.bend as S
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_bud_defs.bend as BD

# Phase E, area E2: general facts of the potential.

# needS holds the last two steps and a pending Ask's step and reads.
def ns_ge(+fa: List<&2, B.Contig>, +T: R.Report, +p: S.StP, +cs: List<&2, String>, +e: Bool, +nx: Pr.Next, +O: String) ->
  {Nat.is_le(Nat.add(2n, BN.RD(nx)), BN.needS(fa, T, S.mkSt(fa, p), cs, e, nx, O)) == True{} : Bool}:
  +RD = BN.RD(nx)
  +WS = BN.WAS(fa, S.mkSt(fa, p), cs)
  +HO = BN.HO(T, O)
  +C = Nat.add(List.length(&2, String, cs), BN.pick(Bool.not(e), 1n))
  +h1 = N.le_trans(RD, Nat.add(RD, WS), Nat.add(HO, Nat.add(RD, WS)), N.le_add_r(RD, WS), N.le_add_l(Nat.add(RD, WS), HO))
  N.le_trans(Nat.add(2n, RD), Nat.add(2n, Nat.add(HO, Nat.add(RD, WS))), Nat.add(C, Nat.add(2n, Nat.add(HO, Nat.add(RD, WS)))),
    N.le_add_mono_l(2n, RD, Nat.add(HO, Nat.add(RD, WS)), h1), N.le_add_l(Nat.add(2n, Nat.add(HO, Nat.add(RD, WS))), C))

law plus_ge:
  for +a: Nat
  for +n: Nat
  for +k: Nat
  for +h: {Nat.is_le(a, n) == True{} : Bool}
  {Nat.is_le(a, Nat.add(n, k)) == True{} : Bool}

def plus_ge(a, n, k, h):
  N.le_trans(a, n, Nat.add(n, k), h, N.le_add_r(n, k))

def need_ge(+fa: List<&2, B.Contig>, +T: R.Report, +x: WD.WPic, +cs: List<&2, String>, +ef: Bool, +nx: Pr.Next, +O: String) ->
  {Nat.is_le(Nat.add(2n, BN.RD(nx)), BD.needW(fa, T, WD.mkWSt(fa, x), cs, ef, nx, O)) == True{} : Bool}:
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      plus_ge(Nat.add(2n, BN.RD(nx)), BN.needS(fa, T, S.mkSt(fa, p), cs, ef, nx, O), BD.XK(cs), ns_ge(fa, T, p, cs, ef, nx, O))
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      +L = List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs))), cs)
      plus_ge(Nat.add(2n, BN.RD(nx)), Nat.add(BN.needS(fa, T, S.mkSt(fa, p), L, False{}, nx, O), Nat.add(BD.kx(k), 4n)), BD.XK(cs),
        plus_ge(Nat.add(2n, BN.RD(nx)), BN.needS(fa, T, S.mkSt(fa, p), L, False{}, nx, O), Nat.add(BD.kx(k), 4n), ns_ge(fa, T, p, L, False{}, nx, O)))
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      +L = List.append(&2, String, BD.plts(PT.mkPls(ps)), cs)
      plus_ge(Nat.add(2n, BN.RD(nx)), BN.needS(fa, T, S.mkSt(fa, p), L, False{}, nx, O), BD.XK(cs), ns_ge(fa, T, p, L, False{}, nx, O))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, +s}}:
      +L = List.append(&2, String, BD.tots(PT.mkTOuts(fa, ps, xs)), cs)
      plus_ge(Nat.add(2n, BN.RD(nx)), Nat.add(BN.needS(fa, T, S.mkSt(fa, p), L, False{}, nx, O), BN.pick(s, 1n)), BD.XK(cs),
        plus_ge(Nat.add(2n, BN.RD(nx)), BN.needS(fa, T, S.mkSt(fa, p), L, False{}, nx, O), BN.pick(s, 1n), ns_ge(fa, T, p, L, False{}, nx, O)))
