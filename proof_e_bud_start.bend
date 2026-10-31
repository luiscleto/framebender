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
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_run.bend as BR
import ./proof_b_budget_dig.bend as G
import ./proof_b_bud_start.bend as BSt
import ./proof_base.bend as PB
import lawful-bytes@0.1.0.0/bytes.bend as BY
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
law half:
  for +u: Nat
  for +A: Nat
  for +AL: Nat
  for +hA: {Nat.is_le(A, AL) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.mul(6n, u), Nat.add(Nat.mul(63n, 1n+u), Nat.add(61n, A))), Nat.mul(124n, Nat.add(1n+u, AL))) == True{} : Bool}

def half(u, A, AL, hA):
  +M63 = Nat.mul(63n, 1n+u)
  +X6 = Nat.mul(6n, u)
  # left: 6u + (M63 + (61 + A)) = M63 + (61 + (6u + A))
  +e1 = Equal.trans(Nat, Nat.add(X6, Nat.add(M63, Nat.add(61n, A))), Nat.add(M63, Nat.add(X6, Nat.add(61n, A))), Nat.add(M63, Nat.add(61n, Nat.add(X6, A))),
    Equal.trans(Nat, Nat.add(X6, Nat.add(M63, Nat.add(61n, A))), Nat.add(Nat.add(X6, M63), Nat.add(61n, A)), Nat.add(M63, Nat.add(X6, Nat.add(61n, A))),
      Equal.sym(Nat, Nat.add(Nat.add(X6, M63), Nat.add(61n, A)), Nat.add(X6, Nat.add(M63, Nat.add(61n, A))), N.add_assoc(X6, M63, Nat.add(61n, A))),
      Equal.trans(Nat, Nat.add(Nat.add(X6, M63), Nat.add(61n, A)), Nat.add(Nat.add(M63, X6), Nat.add(61n, A)), Nat.add(M63, Nat.add(X6, Nat.add(61n, A))),
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(61n, A)), Nat.add(X6, M63), Nat.add(M63, X6), N.add_comm(X6, M63)),
        N.add_assoc(M63, X6, Nat.add(61n, A)))),
    Equal.cong(Nat, Nat, z => Nat.add(M63, z), Nat.add(X6, Nat.add(61n, A)), Nat.add(61n, Nat.add(X6, A)),
      Equal.trans(Nat, Nat.add(X6, Nat.add(61n, A)), Nat.add(Nat.add(X6, 61n), A), Nat.add(61n, Nat.add(X6, A)),
        Equal.sym(Nat, Nat.add(Nat.add(X6, 61n), A), Nat.add(X6, Nat.add(61n, A)), N.add_assoc(X6, 61n, A)),
        Equal.trans(Nat, Nat.add(Nat.add(X6, 61n), A), Nat.add(Nat.add(61n, X6), A), Nat.add(61n, Nat.add(X6, A)),
          Equal.cong(Nat, Nat, z => Nat.add(z, A), Nat.add(X6, 61n), Nat.add(61n, X6), N.add_comm(X6, 61n)),
          N.add_assoc(61n, X6, A)))))
  # right: 124 (1 + u + AL) = (M63 + (61 + 61 u)) + 124 AL
  +R124 = Nat.add(M63, Nat.add(61n, Nat.mul(61n, u)))
  +e2 = Equal.trans(Nat, Nat.mul(124n, Nat.add(1n+u, AL)), Nat.add(Nat.mul(124n, 1n+u), Nat.mul(124n, AL)), Nat.add(R124, Nat.mul(124n, AL)),
    N.mul_add(124n, 1n+u, AL),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(124n, AL)), Nat.mul(124n, 1n+u), R124,
      Equal.trans(Nat, Nat.mul(Nat.add(63n, 61n), 1n+u), Nat.add(M63, Nat.mul(61n, 1n+u)), R124,
        N.mul_add_r(63n, 61n, 1n+u),
        Equal.cong(Nat, Nat, z => Nat.add(M63, z), Nat.mul(61n, 1n+u), Nat.add(61n, Nat.mul(61n, u)), N.mul_succ_r(61n, u)))))
  # (M63 + (61 + 61u)) + 124 AL = M63 + (61 + (61u + 124 AL))
  +e3 = Equal.trans(Nat, Nat.add(R124, Nat.mul(124n, AL)), Nat.add(M63, Nat.add(Nat.add(61n, Nat.mul(61n, u)), Nat.mul(124n, AL))), Nat.add(M63, Nat.add(61n, Nat.add(Nat.mul(61n, u), Nat.mul(124n, AL)))),
    N.add_assoc(M63, Nat.add(61n, Nat.mul(61n, u)), Nat.mul(124n, AL)),
    Equal.cong(Nat, Nat, z => Nat.add(M63, z), Nat.add(Nat.add(61n, Nat.mul(61n, u)), Nat.mul(124n, AL)), Nat.add(61n, Nat.add(Nat.mul(61n, u), Nat.mul(124n, AL))),
      N.add_assoc(61n, Nat.mul(61n, u), Nat.mul(124n, AL))))
  +hx = N.le_mul_r(6n, 61n, u, {==})
  +hz = N.le_trans(A, AL, Nat.mul(124n, AL), hA, BSt.le_124(AL))
  +core = N.le_add_mono_l(M63, Nat.add(61n, Nat.add(X6, A)), Nat.add(61n, Nat.add(Nat.mul(61n, u), Nat.mul(124n, AL))),
    N.le_add_mono_l(61n, Nat.add(X6, A), Nat.add(Nat.mul(61n, u), Nat.mul(124n, AL)), BSt.add2(X6, Nat.mul(61n, u), A, Nat.mul(124n, AL), hx, hz)))
  +L0 = Nat.add(X6, Nat.add(M63, Nat.add(61n, A)))
  +L1 = Nat.add(M63, Nat.add(61n, Nat.add(X6, A)))
  +R1 = Nat.add(R124, Nat.mul(124n, AL))
  +R2 = Nat.add(M63, Nat.add(61n, Nat.add(Nat.mul(61n, u), Nat.mul(124n, AL))))
  %Equal.sym(Nat, L0, L1, e1) : {Nat.is_le(_, Nat.mul(124n, Nat.add(1n+u, AL))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(124n, Nat.add(1n+u, AL)), R1, e2) : {Nat.is_le(L1, _) == True{} : Bool}
  %Equal.sym(Nat, R1, R2, e3) : {Nat.is_le(L1, _) == True{} : Bool}
  core

law twelve:
  for +u: Nat
  for +OB: Nat
  for +Y: Nat
  for +h: {Nat.is_le(Nat.add(Nat.mul(6n, u), OB), Y) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.mul(12n, u), Nat.add(OB, OB)), Nat.add(Y, Y)) == True{} : Bool}

def twelve(u, OB, Y, h):
  +X6 = Nat.mul(6n, u)
  +e12 = Equal.trans(Nat, Nat.mul(12n, u), Nat.mul(Nat.add(6n, 6n), u), Nat.add(X6, X6), {==}, N.mul_add_r(6n, 6n, u))
  # (X6 + X6) + (OB + OB) = (X6 + OB) + (X6 + OB)
  +e = Equal.trans(Nat, Nat.add(Nat.add(X6, X6), Nat.add(OB, OB)), Nat.add(X6, Nat.add(X6, Nat.add(OB, OB))), Nat.add(Nat.add(X6, OB), Nat.add(X6, OB)),
    N.add_assoc(X6, X6, Nat.add(OB, OB)),
    Equal.trans(Nat, Nat.add(X6, Nat.add(X6, Nat.add(OB, OB))), Nat.add(X6, Nat.add(OB, Nat.add(X6, OB))), Nat.add(Nat.add(X6, OB), Nat.add(X6, OB)),
      Equal.cong(Nat, Nat, z => Nat.add(X6, z), Nat.add(X6, Nat.add(OB, OB)), Nat.add(OB, Nat.add(X6, OB)),
        Equal.trans(Nat, Nat.add(X6, Nat.add(OB, OB)), Nat.add(Nat.add(X6, OB), OB), Nat.add(OB, Nat.add(X6, OB)),
          Equal.sym(Nat, Nat.add(Nat.add(X6, OB), OB), Nat.add(X6, Nat.add(OB, OB)), N.add_assoc(X6, OB, OB)),
          N.add_comm(Nat.add(X6, OB), OB))),
      Equal.sym(Nat, Nat.add(Nat.add(X6, OB), Nat.add(X6, OB)), Nat.add(X6, Nat.add(OB, Nat.add(X6, OB))), N.add_assoc(X6, OB, Nat.add(X6, OB)))))
  %Equal.sym(Nat, Nat.mul(12n, u), Nat.add(X6, X6), e12) : {Nat.is_le(Nat.add(_, Nat.add(OB, OB)), Nat.add(Y, Y)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(X6, X6), Nat.add(OB, OB)), Nat.add(Nat.add(X6, OB), Nat.add(X6, OB)), e) : {Nat.is_le(_, Nat.add(Y, Y)) == True{} : Bool}
  BSt.add2(Nat.add(X6, OB), Y, Nat.add(X6, OB), Y, h, h)

# 12 |vcf| + 2 OB within 248 (v + AL).
law room:
  for +vcf: String
  for +o: B.Opts
  for +AL: Nat
  for +hA: {Nat.is_le(String.length(R.args_text(BSt.oargs(o))), AL) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.mul(12n, String.length(vcf)), Nat.add(BR.OB(vcf, o), BR.OB(vcf, o))), Nat.mul(248n, Nat.add(1n+String.length(vcf), AL))) == True{} : Bool}

def room(vcf, o, AL, hA):
  match o:
    case B.Opts{+s, +w, +om_m, +om_z, +args}:
      +u = String.length(vcf)
      +Y = Nat.mul(124n, Nat.add(1n+u, AL))
      %Equal.sym(Nat, Nat.mul(Nat.add(124n, 124n), Nat.add(1n+u, AL)), Nat.add(Y, Y), N.mul_add_r(124n, 124n, Nat.add(1n+u, AL))) :
        {Nat.is_le(Nat.add(Nat.mul(12n, u), Nat.add(BR.OB(vcf, B.Opts{s, w, om_m, om_z, args}), BR.OB(vcf, B.Opts{s, w, om_m, om_z, args}))), _) == True{} : Bool}
      twelve(u, BR.OB(vcf, B.Opts{s, w, om_m, om_z, args}), Y, half(u, String.length(R.args_text(args)), AL, hA))

# HO and the wrapper's share at the start: within v + args_len.
law ho_xk:
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
  {Nat.is_le(Nat.add(BN.HO(L.run(fasta, vcf, o), ""), BD.XK(cs)), Nat.add(1n+String.length(vcf), M.args_len(argv))) == True{} : Bool}

def ho_xk(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, ha, h):
  +n = String.length(R.Report.out(L.run(fasta, vcf, o)))
  +a = Nat.sub(n, String.length(""))
  +X = BD.XK(cs)
  +Y = Nat.add(1n+String.length(vcf), M.args_len(argv))
  +OB = BR.OB(vcf, o)
  +hx = AB.subst(String, z => {Nat.is_le(Nat.mul(256n, X), Nat.mul(12n, String.length(z))) == True{} : Bool}, String.concat(cs), vcf, h, xk_le(cs))
  +hx2 = AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(12n, String.length(vcf))) == True{} : Bool}, Nat.mul(256n, X), Nat.mul(X, 256n), N.mul_comm(256n, X), hx)
  +ha2 = N.le_trans(a, n, Nat.add(OB, OB), BSt.sub0_le(n), BR.out_len(dfs, fasta, vcf, o))
  +hs = N.le_trans(Nat.add(Nat.mul(X, 256n), a), Nat.add(Nat.mul(12n, String.length(vcf)), Nat.add(OB, OB)), Nat.mul(248n, Y),
    BSt.add2(Nat.mul(X, 256n), Nat.mul(12n, String.length(vcf)), a, Nat.add(OB, OB), hx2, ha2),
    room(vcf, o, M.args_len(argv), BSt.args_le(argv, o, ref, vcfpath, ha)))
  +hd = BSt.div_le(Nat.add(Nat.mul(X, 256n), a), Y, 256n, {==}, hs)
  %Equal.sym(Nat, Nat.add(Nat.div(a, 256n), X), Nat.add(X, Nat.div(a, 256n)), N.add_comm(Nat.div(a, 256n), X)) : {Nat.is_le(_, Y) == True{} : Bool}
  %N.div_add_mul(X, 256n, a, {==}) : {Nat.is_le(_, Y) == True{} : Bool}
  hd

# The start
# =========

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
  {Nat.is_le(BD.needW(B.Fasta.parse(fasta), L.run(fasta, vcf, o), W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}

def start_need(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, ha, h):
  +fa = B.Fasta.parse(fasta)
  +T = L.run(fasta, vcf, o)
  +bd = M.bound(argv, fasta, vcf, cs)
  +ls = BN.lines(Nil{}, Norm.PB{BY.empty(0n)}, False{}, cs)
  +v = Nat.add(1n, String.length(vcf))
  +c1 = Nat.add(List.length(&2, String, cs), 1n)
  +H = BN.HO(T, "")
  +Wv = BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, ls)
  +X = BD.XK(cs)
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {Nat.is_le(Nat.add(BN.needS(fa, T, DD.start_st(dfs, Norm.start.of(_)), cs, False{}, Pr.More{}, ""), X), bd) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(c1, Nat.add(2n, Nat.add(H, Wv))), X), Nat.add(c1, Nat.add(2n, Nat.add(Nat.add(H, X), Wv))), shuffle(c1, H, Wv, X)) :
    {Nat.is_le(_, bd) == True{} : Bool}
  N.le_trans(Nat.add(c1, Nat.add(2n, Nat.add(Nat.add(H, X), Wv))), Nat.add(Nat.add(Nat.add(M.pieces_len(cs), 3n), M.args_len(argv)), Nat.mul(1n+String.length(vcf), Nat.add(String.length(fasta), 3n))), bd,
    BSt.fin(List.length(&2, String, cs), Nat.add(H, X), Wv, M.args_len(argv), v, String.length(fasta), BN.FM(fa),
      ho_xk(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, ha, h),
      N.le_trans(Wv, BN.LAs(fa, ls), Nat.mul(v, BN.ZW(fa)), BSt.wa_le(fa, ls), BSt.las_cs(fa, cs, vcf, h)),
      BSt.fa_fm(fasta)),
    N.le_add_r(Nat.add(Nat.add(Nat.add(M.pieces_len(cs), 3n), M.args_len(argv)), Nat.mul(1n+String.length(vcf), Nat.add(String.length(fasta), 3n))), M.split_room(M.splits.of(B.Args.parse(argv)), vcf)))

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
