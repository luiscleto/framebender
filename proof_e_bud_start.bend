import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_drivedefs.bend as DD
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_run.bend as BR
import ./proof_b_budget_dig.bend as G
import ./proof_b_bud_start.bend as BSt
import ./proof_b_drive.bend as DRV
import ./proof_base.bend as PB
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_e_bud_defs.bend as BD

# Phase E, area E2: the budget at the start. Phase B's bound (proof_b_bud_start)
# gives HO <= v + args_len (v = |vcf| + 1) with room: out_len bounds the
# output by 2 (63 v + 61 + |args text|), about half of 256 v. The wrapper's
# 12 per piece of at least 256 bytes (at most 12 |vcf| / 256) fits in it:
#   256 XK + |T.out| <= 12 |vcf| + 2 (63 v + 61 + A) <= 248 (v + AL).

# The wrapper's share against the file's length
# =============================================

law pk:
  for +c: String
  for +b: Bool
  for +hb: {BD.big(c) == b : Bool}
  {Nat.is_le(Nat.mul(256n, BN.pick(BD.big(c), 12n)), Nat.mul(12n, String.length(c))) == True{} : Bool}

def pk(c, b, hb):
  match b:
    case True{}:
      %Equal.sym(Bool, BD.big(c), True{}, hb) : {Nat.is_le(Nat.mul(256n, BN.pick(_, 12n)), Nat.mul(12n, String.length(c))) == True{} : Bool}
      N.le_mul_l(12n, 256n, String.length(c), hb)
    case False{}:
      %Equal.sym(Bool, BD.big(c), False{}, hb) : {Nat.is_le(Nat.mul(256n, BN.pick(_, 12n)), Nat.mul(12n, String.length(c))) == True{} : Bool}
      N.le_zero_l(Nat.mul(12n, String.length(c)))

law xk_le:
  for +cs: List<&2, String>
  {Nat.is_le(Nat.mul(256n, BD.XK(cs)), Nat.mul(12n, String.length(String.concat(cs)))) == True{} : Bool}

def xk_le(cs):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      +P = BN.pick(BD.big(c), 12n)
      %Equal.sym(Nat, Nat.mul(256n, Nat.add(P, BD.XK(t))), Nat.add(Nat.mul(256n, P), Nat.mul(256n, BD.XK(t))), N.mul_add(256n, P, BD.XK(t))) :
        {Nat.is_le(_, Nat.mul(12n, String.length(String.append(c, String.concat(t))))) == True{} : Bool}
      %Equal.sym(Nat, String.length(String.append(c, String.concat(t))), Nat.add(String.length(c), String.length(String.concat(t))), G.slen_app(c, String.concat(t))) :
        {Nat.is_le(Nat.add(Nat.mul(256n, P), Nat.mul(256n, BD.XK(t))), Nat.mul(12n, _)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(12n, Nat.add(String.length(c), String.length(String.concat(t)))), Nat.add(Nat.mul(12n, String.length(c)), Nat.mul(12n, String.length(String.concat(t)))), N.mul_add(12n, String.length(c), String.length(String.concat(t)))) :
        {Nat.is_le(Nat.add(Nat.mul(256n, P), Nat.mul(256n, BD.XK(t))), _) == True{} : Bool}
      BSt.add2(Nat.mul(256n, P), Nat.mul(12n, String.length(c)), Nat.mul(256n, BD.XK(t)), Nat.mul(12n, String.length(String.concat(t))),
        pk(c, BD.big(c), {==}), xk_le(t))

# The arithmetic
# ==============

# 63 (1 + u) + (61 + (x + A)) within 124 (1 + u) + y + Z for x <= 61 u, A <= Z (y unused slack).
law shuffle:
  for +c1: Nat
  for +H: Nat
  for +Wv: Nat
  for +X: Nat
  {Nat.add(Nat.add(c1, Nat.add(2n, Nat.add(H, Wv))), X) == Nat.add(c1, Nat.add(2n, Nat.add(Nat.add(H, X), Wv))) : Nat}

def shuffle(c1, H, Wv, X):
  +e1 = N.add_assoc(c1, Nat.add(2n, Nat.add(H, Wv)), X)
  +e2 = N.add_assoc(2n, Nat.add(H, Wv), X)
  +e3 = Equal.trans(Nat, Nat.add(Nat.add(H, Wv), X), Nat.add(H, Nat.add(Wv, X)), Nat.add(Nat.add(H, X), Wv),
    N.add_assoc(H, Wv, X),
    Equal.trans(Nat, Nat.add(H, Nat.add(Wv, X)), Nat.add(H, Nat.add(X, Wv)), Nat.add(Nat.add(H, X), Wv),
      Equal.cong(Nat, Nat, z => Nat.add(H, z), Nat.add(Wv, X), Nat.add(X, Wv), N.add_comm(Wv, X)),
      Equal.sym(Nat, Nat.add(Nat.add(H, X), Wv), Nat.add(H, Nat.add(X, Wv)), N.add_assoc(H, X, Wv))))
  Equal.trans(Nat, Nat.add(Nat.add(c1, Nat.add(2n, Nat.add(H, Wv))), X), Nat.add(c1, Nat.add(Nat.add(2n, Nat.add(H, Wv)), X)), Nat.add(c1, Nat.add(2n, Nat.add(Nat.add(H, X), Wv))),
    e1, Equal.cong(Nat, Nat, z => Nat.add(c1, z), Nat.add(Nat.add(2n, Nat.add(H, Wv)), X), Nat.add(2n, Nat.add(Nat.add(H, X), Wv)),
      Equal.trans(Nat, Nat.add(Nat.add(2n, Nat.add(H, Wv)), X), Nat.add(2n, Nat.add(Nat.add(H, Wv), X)), Nat.add(2n, Nat.add(Nat.add(H, X), Wv)),
        e2, Equal.cong(Nat, Nat, z => Nat.add(2n, z), Nat.add(Nat.add(H, Wv), X), Nat.add(Nat.add(H, X), Wv), e3))))

law start_need:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  {Nat.is_le(BD.needW(B.Fasta.parse(fasta), L.run(fasta, vcf, o), W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}

# Phase B's start fit, with the wrapper's 12 per piece of 256 bytes (XK) as
# its extra share K, at start_ok's picture of the start state.
def start_need.k(+dfs: B.Defs, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +fasta: String, +vcf: String, +cs: List<&2, String>,
  +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>},
  +h: {String.concat(cs) == vcf : String},
  so: &p: S.StP -> ({DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
    & ({DD.start_paths(Norm.start(argv)) == Some{DD.Paths{ref, vcfpath}} : Maybe<&2, DD.Paths>}
    & ({DD.more_ok(B.Fasta.parse(fasta), p) == True{} : Bool}
    & ({S.report(B.Fasta.parse(fasta), cs, "", Nil{}, p) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), B.Fasta.parse(fasta), L.defs(String.concat(cs)), o, R.start_st())) : R.Report}
    & {S.guard("", Nil{}, p) == True{} : Bool}))))) ->
  {Nat.is_le(BD.needW(B.Fasta.parse(fasta), L.run(fasta, vcf, o), W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}:
  (+p, s1) = so
  (+hst, s2) = s1
  +fa = B.Fasta.parse(fasta)
  +T = L.run(fasta, vcf, o)
  +bd = M.bound(argv, fasta, vcf, cs)
  +c1 = Nat.add(List.length(&2, String, cs), 1n)
  +H = BN.HO(T, "")
  +X = BD.XK(cs)
  +Wv = BN.WAS(fa, S.mkSt(fa, p), cs)
  +hK = AB.subst(String, z => {Nat.is_le(Nat.mul(256n, X), Nat.mul(12n, String.length(z))) == True{} : Bool}, String.concat(cs), vcf, h, xk_le(cs))
  %Equal.sym(Norm.St, DD.start_st(dfs, Norm.start(argv)), S.mkSt(fa, p), hst) :
    {Nat.is_le(Nat.add(BN.needS(fa, T, _, cs, False{}, Pr.More{}, ""), X), bd) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(c1, Nat.add(2n, Nat.add(H, Wv))), X), Nat.add(c1, Nat.add(2n, Nat.add(Nat.add(H, X), Wv))), shuffle(c1, H, Wv, X)) :
    {Nat.is_le(_, bd) == True{} : Bool}
  BSt.start_fit(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, p, X, ha, h, hst, hK)

def start_need(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, ha, h, hb):
  start_need.k(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, ha, h,
    DRV.start_ok(dfs, B.Fasta.parse(fasta), argv, o, ref, vcfpath, cs, ha, PB.and_true_l(E.all_bytes(argv), Bool.and(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs))), hb)))

law start_bi:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  {BD.biW(W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs) == True{} : Bool}

def start_bi(dfs,argv, o, ref, vcfpath, cs, ha):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) : {BN.biS(DD.start_st(dfs, Norm.start.of(_)), cs) == True{} : Bool}
  BSt.bi0(BN.lines(Nil{}, Norm.PB{BY.empty(0n)}, False{}, cs))
