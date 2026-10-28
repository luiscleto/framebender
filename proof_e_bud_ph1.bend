import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_bud_start.bend as BSt
import ./proof_b_drive_out.bend as DO
import ./proof_b_budget_need.bend as BN
import ./proof_base.bend as PB
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB
import ./proof_e_task.bend as PT
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_step.bend as ST

# Phase E, area E2: helpers for the batch's phases (counts and arithmetic).

law and_mk2:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_mk2(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# VQ with a + W0 is VQ with W0, plus a.
law vq_shift:
  for +T: R.Report
  for +L: List<&2, String>
  for +e: Bool
  for +O: String
  for +a: Nat
  for +W0: Nat
  {ST.VQ(T, L, e, O, Nat.add(a, W0)) == Nat.add(ST.VQ(T, L, e, O, W0), a) : Nat}

def vq_shift(T, L, e, O, a, W0):
  +A = Nat.add(List.length(&2, String, L), BN.pick(Bool.not(e), 1n))
  +H = BN.HO(T, O)
  +e1 = Equal.trans(Nat, Nat.add(H, Nat.add(a, W0)), Nat.add(H, Nat.add(W0, a)), Nat.add(Nat.add(H, W0), a),
    Equal.cong(Nat, Nat, z => Nat.add(H, z), Nat.add(a, W0), Nat.add(W0, a), N.add_comm(a, W0)),
    Equal.sym(Nat, Nat.add(Nat.add(H, W0), a), Nat.add(H, Nat.add(W0, a)), N.add_assoc(H, W0, a)))
  +e2 = Equal.trans(Nat, Nat.add(2n, Nat.add(H, Nat.add(a, W0))), Nat.add(2n, Nat.add(Nat.add(H, W0), a)), Nat.add(Nat.add(2n, Nat.add(H, W0)), a),
    Equal.cong(Nat, Nat, z => Nat.add(2n, z), Nat.add(H, Nat.add(a, W0)), Nat.add(Nat.add(H, W0), a), e1),
    Equal.sym(Nat, Nat.add(Nat.add(2n, Nat.add(H, W0)), a), Nat.add(2n, Nat.add(Nat.add(H, W0), a)), N.add_assoc(2n, Nat.add(H, W0), a)))
  Equal.trans(Nat, Nat.add(A, Nat.add(2n, Nat.add(H, Nat.add(a, W0)))), Nat.add(A, Nat.add(Nat.add(2n, Nat.add(H, W0)), a)), Nat.add(Nat.add(A, Nat.add(2n, Nat.add(H, W0))), a),
    Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.add(2n, Nat.add(H, Nat.add(a, W0))), Nat.add(Nat.add(2n, Nat.add(H, W0)), a), e2),
    Equal.sym(Nat, Nat.add(Nat.add(A, Nat.add(2n, Nat.add(H, W0))), a), Nat.add(A, Nat.add(Nat.add(2n, Nat.add(H, W0)), a)), N.add_assoc(A, Nat.add(2n, Nat.add(H, W0)), a)))

# VQ grows with W0.
law vq_mono:
  for +T: R.Report
  for +L: List<&2, String>
  for +e: Bool
  for +O: String
  for +W1: Nat
  for +W2: Nat
  for +h: {Nat.is_le(W1, W2) == True{} : Bool}
  {Nat.is_le(ST.VQ(T, L, e, O, W1), ST.VQ(T, L, e, O, W2)) == True{} : Bool}

def vq_mono(T, L, e, O, W1, W2, h):
  ST.vq_le(Nat.add(List.length(&2, String, L), BN.pick(Bool.not(e), 1n)), Nat.add(BN.HO(T, O), W1), Nat.add(BN.HO(T, O), W2), N.le_add_mono_l(BN.HO(T, O), W1, W2, h))

# A good state's options are bytes (WF's last test).
law wf_args:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  {E.all_bytes(S.opts_args(S.StP.o(p))) == True{} : Bool}

def wf_args(fa, p, hw):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      DO.x9_8(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
        Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)

# Counts
# ======

# 7k is at least k + k.
law kx_ge:
  for +k: Nat
  {Nat.is_le(Nat.add(k, k), BD.kx(k)) == True{} : Bool}

def kx_ge(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      +e = Equal.trans(Nat, Nat.add(1n+j, 1n+j), 1n+Nat.add(j, 1n+j), 1n+(1n+Nat.add(j, j)), {==},
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(j, 1n+j), 1n+Nat.add(j, j), N.add_succ(j, j)))
      %Equal.sym(Nat, Nat.add(1n+j, 1n+j), 1n+(1n+Nat.add(j, j)), e) : {Nat.is_le(_, BD.kx(1n+j)) == True{} : Bool}
      N.le_trans(1n+(1n+Nat.add(j, j)), Nat.add(2n, BD.kx(j)), Nat.add(7n, BD.kx(j)),
        N.le_add_mono_l(2n, Nat.add(j, j), BD.kx(j), kx_ge(j)), N.le_add_mono_r(BD.kx(j), 2n, 7n, {==}))

# Each piece of a plan has at most two reads.
law two_le:
  for +rs: List<&2, Pr.Req>
  for +h: {PT.two(rs) == True{} : Bool}
  {Nat.is_le(List.length(&2, Pr.Req, rs), 2n) == True{} : Bool}

def two_le(rs, h):
  match rs:
    case Nil{}:
      Empty.absurd({Nat.is_le(0n, 2n) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+a, Nil{}}:
      {==}
    case Con{+a, Con{+b, Nil{}}}:
      {==}
    case Con{+a, Con{+b, Con{+c, +t}}}:
      Empty.absurd({Nat.is_le(List.length(&2, Pr.Req, a <> (b <> (c <> t))), 2n) == True{} : Bool}, PB.false_ne_true(h))

law pc_le:
  for +p: PT.Pc
  for +X: String
  for h: PT.PcOK(p, X)
  {Nat.is_le(List.length(&2, Pr.Req, PT.Pc.rs(p)), 2n) == True{} : Bool}

def pc_le(p, X, h):
  match p:
    case PT.Pc{+c, +rs, True{}, +k, +c0, +l}:
      (a1, h1) = h
      two_le(rs, PB.and_true_r(PT.rs_ok(rs), PT.two(rs), a1))
    case PT.Pc{+c, +rs, False{}, +k, +c0, +l}:
      AB.subst(List<&2, Pr.Req>, z => {Nat.is_le(List.length(&2, Pr.Req, z), 2n) == True{} : Bool}, Nil{}, rs, Equal.sym(List<&2, Pr.Req>, rs, Nil{}, h), {==})

law reqs_le:
  for +ps: List<&2, PT.Pc>
  for +dcs: List<&2, String>
  for h: PT.PcsOK(ps, dcs)
  {Nat.is_le(List.length(&2, Pr.Req, PT.reqs_of(ps)), Nat.add(List.length(&2, PT.Pc, ps), List.length(&2, PT.Pc, ps))) == True{} : Bool}

def reqs_le(ps, dcs, h):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      (h1, h2) = h
      +m = List.length(&2, PT.Pc, t)
      +r1 = List.length(&2, Pr.Req, PT.Pc.rs(p))
      +r2 = List.length(&2, Pr.Req, PT.reqs_of(t))
      %Equal.sym(Nat, List.length(&2, Pr.Req, List.append(&2, Pr.Req, PT.Pc.rs(p), PT.reqs_of(t))), Nat.add(r1, r2), PB.length_append(Pr.Req, PT.Pc.rs(p), PT.reqs_of(t))) :
        {Nat.is_le(_, Nat.add(1n+m, 1n+m)) == True{} : Bool}
      +e = Equal.trans(Nat, Nat.add(1n+m, 1n+m), 1n+Nat.add(m, 1n+m), Nat.add(2n, Nat.add(m, m)), {==},
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(m, 1n+m), 1n+Nat.add(m, m), N.add_succ(m, m)))
      %Equal.sym(Nat, Nat.add(1n+m, 1n+m), Nat.add(2n, Nat.add(m, m)), e) : {Nat.is_le(Nat.add(r1, r2), _) == True{} : Bool}
      BSt.add2(r1, 2n, r2, Nat.add(m, m), pc_le(p, String.concat(List.append(&2, String, PT.texts(t), dcs)), h1), reqs_le(t, dcs, h2))

law len_texts:
  for +ps: List<&2, PT.Pc>
  {List.length(&2, String, PT.texts(ps)) == List.length(&2, PT.Pc, ps) : Nat}

def len_texts(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, String, PT.texts(t)), List.length(&2, PT.Pc, t), len_texts(t))

law len_rg:
  for +l: List<&2, String>
  for +acc: List<&2, String>
  {List.length(&2, String, List.reverse.go(&2, String, l, acc)) == Nat.add(List.length(&2, String, l), List.length(&2, String, acc)) : Nat}

def len_rg(l, acc):
  match l:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, String, List.reverse.go(&2, String, t, h <> acc)), Nat.add(List.length(&2, String, t), 1n+List.length(&2, String, acc)), 1n+Nat.add(List.length(&2, String, t), List.length(&2, String, acc)),
        len_rg(t, h <> acc), N.add_succ(List.length(&2, String, t), List.length(&2, String, acc)))

law ab_app:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +hx: {E.all_bytes(xs) == True{} : Bool}
  for +hy: {E.all_bytes(ys) == True{} : Bool}
  {E.all_bytes(List.append(&2, String, xs, ys)) == True{} : Bool}

def ab_app(xs, ys, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +t}:
      and_mk2(E.is_bytes(x), E.all_bytes(List.append(&2, String, t, ys)), PB.and_true_l(E.is_bytes(x), E.all_bytes(t), hx), ab_app(t, ys, PB.and_true_r(E.is_bytes(x), E.all_bytes(t), hx), hy))

law po_app:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +hx: {E.pieces_ok(xs) == True{} : Bool}
  for +hy: {E.pieces_ok(ys) == True{} : Bool}
  {E.pieces_ok(List.append(&2, String, xs, ys)) == True{} : Bool}

def po_app(xs, ys, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +t}:
      and_mk2(E.le31(String.length(x)), E.pieces_ok(List.append(&2, String, t, ys)), PB.and_true_l(E.le31(String.length(x)), E.pieces_ok(t), hx), po_app(t, ys, PB.and_true_r(E.le31(String.length(x)), E.pieces_ok(t), hx), hy))
