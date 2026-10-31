import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BDs
import ./proof_b_budget_step.bend as BS
import ./proof_b_enc.bend as EN
import ./proof_base.bend as PB
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-halves@0.1.0.0/halves.bend as HH
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as QB
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_api.bend as API
import ./proof_e_bud_step.bend as ST
import ./proof_e_bud_none.bend as BNo
import ./proof_e_bud_list.bend as LI
import ./proof_e_bud_ph1.bend as H1
import ./proof_e_bud_plan.bend as PL
import ./proof_e_bud_seq.bend as SQ
import ./proof_e_bud_comb.bend as CB
import ./proof_e_mach_dup.bend as DU
import ./proof_e_wrap_col.bend as WL

# Phase E, area E2: the batch's phases. Collecting (a piece taken, or the
# batch closed by a piece or the end of the file), the plan's Ask answered,
# the combine's Ask{[]} answered, and Q's own Ask in the middle of a piece.

# Arithmetic
# ==========

# ((V0 + (d + A)) + X) + 1 <= (V0 + A) + (e + X) when d + 1 <= e.
law ar_dx:
  for +V0: Nat
  for +A: Nat
  for +X: Nat
  for +d: Nat
  for +e: Nat
  for +h: {Nat.is_le(Nat.add(d, 1n), e) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(Nat.add(V0, Nat.add(d, A)), X), Nat.add(0n, 1n)), Nat.add(Nat.add(V0, A), Nat.add(e, X))) == True{} : Bool}

def ar_dx(V0, A, X, d, e, h):
  +Y = Nat.add(V0, A)
  +e1 = Equal.trans(Nat, Nat.add(V0, Nat.add(d, A)), Nat.add(d, Y), Nat.add(Y, d), N.add_left_comm(V0, d, A), N.add_comm(d, Y))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(Y, d), X), Nat.add(Y, Nat.add(d, X)), Nat.add(Y, Nat.add(d, X)), N.add_assoc(Y, d, X), {==})
  +e3 = Equal.trans(Nat, Nat.add(Nat.add(d, X), 1n), Nat.add(d, Nat.add(X, 1n)), Nat.add(Nat.add(d, 1n), X),
    N.add_assoc(d, X, 1n),
    Equal.trans(Nat, Nat.add(d, Nat.add(X, 1n)), Nat.add(d, Nat.add(1n, X)), Nat.add(Nat.add(d, 1n), X),
      Equal.cong(Nat, Nat, z => Nat.add(d, z), Nat.add(X, 1n), Nat.add(1n, X), N.add_comm(X, 1n)),
      Equal.sym(Nat, Nat.add(Nat.add(d, 1n), X), Nat.add(d, Nat.add(1n, X)), N.add_assoc(d, 1n, X))))
  +e4 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(V0, Nat.add(d, A)), X), 1n), Nat.add(Nat.add(Nat.add(Y, d), X), 1n), Nat.add(Y, Nat.add(Nat.add(d, 1n), X)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, X), 1n), Nat.add(V0, Nat.add(d, A)), Nat.add(Y, d), e1),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Y, d), X), 1n), Nat.add(Nat.add(Y, Nat.add(d, X)), 1n), Nat.add(Y, Nat.add(Nat.add(d, 1n), X)),
      Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(Nat.add(Y, d), X), Nat.add(Y, Nat.add(d, X)), e2),
      Equal.trans(Nat, Nat.add(Nat.add(Y, Nat.add(d, X)), 1n), Nat.add(Y, Nat.add(Nat.add(d, X), 1n)), Nat.add(Y, Nat.add(Nat.add(d, 1n), X)),
        N.add_assoc(Y, Nat.add(d, X), 1n),
        Equal.cong(Nat, Nat, z => Nat.add(Y, z), Nat.add(Nat.add(d, X), 1n), Nat.add(Nat.add(d, 1n), X), e3))))
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(V0, Nat.add(d, A)), X), 1n), Nat.add(Y, Nat.add(Nat.add(d, 1n), X)), e4) : {Nat.is_le(_, Nat.add(Y, Nat.add(e, X))) == True{} : Bool}
  N.le_add_mono_l(Y, Nat.add(Nat.add(d, 1n), X), Nat.add(e, X), N.le_add_mono_r(X, Nat.add(d, 1n), e, h))

# ((V0 + a) + X) + 1 <= (V0 + B) + (P + X) when a + 1 <= B.
law ar_plan:
  for +V0: Nat
  for +a: Nat
  for +B0: Nat
  for +X: Nat
  for +P0: Nat
  for +h: {Nat.is_le(Nat.add(a, 1n), B0) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(Nat.add(V0, a), X), Nat.add(0n, 1n)), Nat.add(Nat.add(V0, B0), Nat.add(P0, X))) == True{} : Bool}

def ar_plan(V0, a, B0, X, P0, h):
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(V0, a), X), 1n), Nat.add(Nat.add(V0, a), Nat.add(X, 1n)), Nat.add(V0, Nat.add(Nat.add(a, 1n), X)),
    N.add_assoc(Nat.add(V0, a), X, 1n),
    Equal.trans(Nat, Nat.add(Nat.add(V0, a), Nat.add(X, 1n)), Nat.add(V0, Nat.add(a, Nat.add(X, 1n))), Nat.add(V0, Nat.add(Nat.add(a, 1n), X)),
      N.add_assoc(V0, a, Nat.add(X, 1n)),
      Equal.cong(Nat, Nat, z => Nat.add(V0, z), Nat.add(a, Nat.add(X, 1n)), Nat.add(Nat.add(a, 1n), X),
        Equal.trans(Nat, Nat.add(a, Nat.add(X, 1n)), Nat.add(a, Nat.add(1n, X)), Nat.add(Nat.add(a, 1n), X),
          Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(X, 1n), Nat.add(1n, X), N.add_comm(X, 1n)),
          Equal.sym(Nat, Nat.add(Nat.add(a, 1n), X), Nat.add(a, Nat.add(1n, X)), N.add_assoc(a, 1n, X))))))
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(V0, a), X), 1n), Nat.add(V0, Nat.add(Nat.add(a, 1n), X)), e1) : {Nat.is_le(_, Nat.add(Nat.add(V0, B0), Nat.add(P0, X))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(V0, B0), Nat.add(P0, X)), Nat.add(V0, Nat.add(B0, Nat.add(P0, X))), N.add_assoc(V0, B0, Nat.add(P0, X))) : {Nat.is_le(Nat.add(V0, Nat.add(Nat.add(a, 1n), X)), _) == True{} : Bool}
  N.le_add_mono_l(V0, Nat.add(Nat.add(a, 1n), X), Nat.add(B0, Nat.add(P0, X)),
    N.le_trans(Nat.add(Nat.add(a, 1n), X), Nat.add(B0, X), Nat.add(B0, Nat.add(P0, X)), N.le_add_mono_r(X, Nat.add(a, 1n), B0, h),
      N.le_add_mono_l(B0, X, Nat.add(P0, X), N.le_add_l(X, P0))))

# (1 + ((j + 1) + (j + 1))) + 1 <= 7j + 4: a full batch's plan.
law ar_k1:
  for +j: Nat
  {Nat.is_le(Nat.add(1n+Nat.add(Nat.add(j, 1n), Nat.add(j, 1n)), 1n), Nat.add(BD.kx(j), 4n)) == True{} : Bool}

def ar_k1(j):
  +jj = Nat.add(j, j)
  %Equal.sym(Nat, Nat.add(j, 1n), 1n+j, N.add_one(j)) : {Nat.is_le(Nat.add(1n+Nat.add(_, _), 1n), Nat.add(BD.kx(j), 4n)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(j, 1n+j), 1n+jj, N.add_succ(j, j)) : {Nat.is_le(Nat.add(1n+(1n+_), 1n), Nat.add(BD.kx(j), 4n)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(jj, 1n), 1n+jj, N.add_one(jj)) : {Nat.is_le(1n+(1n+(1n+_)), Nat.add(BD.kx(j), 4n)) == True{} : Bool}
  %N.add_comm(4n, BD.kx(j)) : {Nat.is_le(1n+(1n+(1n+(1n+jj))), _) == True{} : Bool}
  H1.kx_ge(j)

# (1 + (j + j)) + 1 <= 7j + 4: a batch closed by the end of the file.
law ar_k0:
  for +j: Nat
  {Nat.is_le(Nat.add(1n+Nat.add(j, j), 1n), Nat.add(BD.kx(j), 4n)) == True{} : Bool}

def ar_k0(j):
  +jj = Nat.add(j, j)
  %Equal.sym(Nat, Nat.add(jj, 1n), 1n+jj, N.add_one(jj)) : {Nat.is_le(1n+_, Nat.add(BD.kx(j), 4n)) == True{} : Bool}
  %N.add_comm(4n, BD.kx(j)) : {Nat.is_le(1n+(1n+jj), _) == True{} : Bool}
  N.le_trans(1n+(1n+jj), 1n+(1n+BD.kx(j)), Nat.add(4n, BD.kx(j)), H1.kx_ge(j), N.le_add_mono_r(BD.kx(j), 2n, 4n, {==}))

law or_false_r2:
  for +a: Bool
  for +b: Bool
  for +h: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_false_r2(a, b, h):
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, PB.true_ne_false(h))
    case False{}:
      h

# A piece not shorter than minp() bytes is big.
law big_not_lt:
  for +c: String
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +h: {U32.is_lt(U32.from_nat(String.length(c)), 256) == False{} : Bool}
  {BD.big(c) == True{} : Bool}

def big_not_lt(c, hcb, hcn, h):
  +n = U32.from_nat(String.length(c))
  +h1 = Equal.trans(Bool, Nat.is_lt(U32.to_nat(n), U32.to_nat(256)), U32.is_lt(n, 256), False{}, Equal.sym(Bool, U32.is_lt(n, 256), Nat.is_lt(U32.to_nat(n), U32.to_nat(256)), U.is_lt_to_nat(n, 256)), h)
  AB.subst(Nat, z => {Nat.is_le(256n, z) == True{} : Bool}, U32.to_nat(n), String.length(c), BNo.nat_enc.k(c, EN.enc_ok(c, hcb, hcn)), N.not_lt_le(U32.to_nat(n), U32.to_nat(256), h1))

# Collecting
# ==========

# A step of Q handed out while collecting the pieces hs2 (newest first).
law wrap_colk:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +W0: Nat
  for +hs2: List<&2, String>
  for +k2: Nat
  for s: Norm.Step
  for h: BDs.BudS(fa, T, List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs2))), cs), O, W0, s)
  ST.BudW(fa, T, cs, False{}, O, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs2))), cs), False{}, O, W0), Nat.add(BD.kx(k2), 4n)), BD.XK(cs)), W.wrap(s, W.BCol{PT.encs(hs2), k2}))

def wrap_colk(fa, T, cs, O, W0, hs2, k2, s, h):
  match s:
    case Norm.Step{st, b, +ns, +nx}:
      (hbi, k) = h
      +La = List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs2))), cs)
      hnf => (hbi, +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs2))), cs), False{}, O, W0), Nat.add(BD.kx(k2), 4n)), BD.XK(cs))) == True{} : Bool};
        ST.needs_le2(fa, T, La, False{}, O, W0, st, nx, String.append(O, t), Nat.add(BD.kx(k2), 4n), BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, La)))

def Lb(+hs: List<&2, String>, +c: String, +cs: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs))), c <> cs)

def Lb2(+hs: List<&2, String>, +c: String, +cs: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, List.reverse(&2, String, hs), c <> cs)

# The piece taken: one more held.
law col_more:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for +hbts: {BD.bts(PT.encs(hs)) == hs : List<&2, String>}
  for +hbi: {BN.biS(S.mkSt(fa, p), Lb(hs, c, cs)) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +hbig: {BD.big(c) == True{} : Bool}
  API.KontW(dfs, fa, T, W.wrap(Norm.out(S.mkSt(fa, p), Pr.More{}), W.BCol{E.enc(c) <> PT.encs(hs), 1n+k}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O), O, N)

def col_more(dfs,fa, T, c, cs, O, N, p, hs, k, hbts, hbi, hcb, hcn, hbig):
  +La = List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(c <> hs))), cs)
  +L2 = Lb2(hs, c, cs)
  +ecs = Equal.trans(List<&2, String>, NR.chars(D.view(E.enc(c))) <> BD.bts(PT.encs(hs)), c <> BD.bts(PT.encs(hs)), c <> hs,
    Equal.cong(String, List<&2, String>, z => z <> BD.bts(PT.encs(hs)), NR.chars(D.view(E.enc(c))), c, BNo.chars_enc(c, hcb, hcn)),
    Equal.cong(List<&2, String>, List<&2, String>, z => c <> z, BD.bts(PT.encs(hs)), hs, hbts))
  +eqA = Equal.trans(List<&2, String>, La, List.append(&2, String, List.reverse(&2, String, c <> hs), cs), L2,
    Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, List.reverse(&2, String, z), cs), NR.chars(D.view(E.enc(c))) <> BD.bts(PT.encs(hs)), c <> hs, ecs),
    LI.revapp(c, hs, cs))
  +eqB = Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, List.reverse(&2, String, z), c <> cs), BD.bts(PT.encs(hs)), hs, hbts)
  +hbi2 = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, Lb(hs, c, cs), L2, eqB, hbi)
  +hbiA = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, L2, La, Equal.sym(List<&2, String>, La, L2, eqA), hbi2)
  +W0 = BDs.WP(fa, La, p)
  +V = Nat.add(Nat.add(ST.VQ(T, La, False{}, O, W0), Nat.add(BD.kx(1n+k), 4n)), BD.XK(cs))
  +A = Nat.add(BD.kx(k), 4n)
  +X = BD.XK(cs)
  +h0 = ar_dx(ST.VQ(T, L2, False{}, O, BDs.WP(fa, L2, p)), A, X, 7n, 12n, {==})
  +h1 = AB.subst(List<&2, String>, z => {Nat.is_le(Nat.add(Nat.add(Nat.add(ST.VQ(T, z, False{}, O, BDs.WP(fa, z, p)), Nat.add(7n, A)), X), Nat.add(0n, 1n)), Nat.add(Nat.add(ST.VQ(T, L2, False{}, O, BDs.WP(fa, L2, p)), A), Nat.add(12n, X))) == True{} : Bool},
    L2, La, Equal.sym(List<&2, String>, La, L2, eqA), h0)
  +h2 = AB.subst(List<&2, String>, z => {Nat.is_le(Nat.add(V, Nat.add(0n, 1n)), Nat.add(Nat.add(ST.VQ(T, z, False{}, O, BDs.WP(fa, z, p)), A), Nat.add(12n, X))) == True{} : Bool},
    L2, Lb(hs, c, cs), Equal.sym(List<&2, String>, Lb(hs, c, cs), L2, eqB), h1)
  +hv = AB.subst(Bool, z => {Nat.is_le(Nat.add(V, Nat.add(0n, 1n)), Nat.add(Nat.add(ST.VQ(T, Lb(hs, c, cs), False{}, O, BDs.WP(fa, Lb(hs, c, cs), p)), A), Nat.add(BN.pick(z, 12n), X))) == True{} : Bool},
    True{}, BD.big(c), Equal.sym(Bool, BD.big(c), True{}, hbig), h2)
  ST.kont_of(dfs, fa, T, W.wrap(Norm.out(S.mkSt(fa, p), Pr.More{}), W.BCol{PT.encs(c <> hs), 1n+k}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O), V, O, N,
    wrap_colk(fa, T, cs, O, W0, c <> hs, 1n+k, Norm.out(S.mkSt(fa, p), Pr.More{}), BS.out_bud(fa, T, La, O, p, Pr.More{}, W0, hbiA, N.le_refl(W0))),
    hv)

# The plan's bound against the collecting state's need: ((V0 + a) + X) + 1
# <= (V0' + B) + (P + X), V0 over LH and V0' over Lb, LH == Lb.
law plan_n1:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +p: S.StP
  for +Hs: List<&2, String>
  for +L1: List<&2, String>
  for +B0: Nat
  for +P0: Nat
  for +eqL: {List.append(&2, String, Hs, cs) == L1 : List<&2, String>}
  for +h: {Nat.is_le(Nat.add(1n+Nat.add(List.length(&2, String, Hs), List.length(&2, String, Hs)), 1n), B0) == True{} : Bool}
  {Nat.is_le(Nat.add(PL.VH(fa, T, cs, O, p, Hs), Nat.add(0n, 1n)), Nat.add(Nat.add(ST.VQ(T, L1, False{}, O, BDs.WP(fa, L1, p)), B0), Nat.add(P0, BD.XK(cs)))) == True{} : Bool}

def plan_n1(fa, T, cs, O, p, Hs, L1, B0, P0, eqL, h):
  +LH = List.append(&2, String, Hs, cs)
  +a = Nat.add(1n, Nat.add(List.length(&2, String, Hs), List.length(&2, String, Hs)))
  +X = BD.XK(cs)
  +h0 = ar_plan(ST.VQ(T, LH, False{}, O, BDs.WP(fa, LH, p)), a, B0, X, P0, h)
  +h1 = AB.subst(List<&2, String>, z => {Nat.is_le(Nat.add(Nat.add(Nat.add(ST.VQ(T, LH, False{}, O, BDs.WP(fa, LH, p)), a), X), Nat.add(0n, 1n)), Nat.add(Nat.add(ST.VQ(T, z, False{}, O, BDs.WP(fa, z, p)), B0), Nat.add(P0, X))) == True{} : Bool},
    LH, L1, eqL, h0)
  %Equal.sym(Nat, ST.VQ(T, LH, False{}, O, Nat.add(a, BDs.WP(fa, LH, p))), Nat.add(ST.VQ(T, LH, False{}, O, BDs.WP(fa, LH, p)), a), H1.vq_shift(T, LH, False{}, O, a, BDs.WP(fa, LH, p))) : {Nat.is_le(Nat.add(Nat.add(_, X), Nat.add(0n, 1n)), Nat.add(Nat.add(ST.VQ(T, L1, False{}, O, BDs.WP(fa, L1, p)), B0), Nat.add(P0, X))) == True{} : Bool}
  h1

# The batch closed by a piece (the kmax()-th, or a short one).
law col_close:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, Lb2(hs, c, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  for +hk: {k == List.length(&2, String, hs) : Nat}
  for +hbts: {BD.bts(PT.encs(hs)) == hs : List<&2, String>}
  for +hbi: {BN.biS(S.mkSt(fa, p), Lb(hs, c, cs)) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  API.KontW(dfs, fa, T, W.plan(S.mkSt(fa, p), PT.encs(List.reverse.go(&2, String, c <> hs, Nil{})), False{}, dfs), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O), O, N)

def col_close(dfs,fa, T, c, cs, O, N, p, hs, k, hb, hm, hst, hg, hr, hby, hk, hbts, hbi, hcb, hcn):
  +Hs = List.reverse.go(&2, String, c <> hs, Nil{})
  +rh = List.reverse(&2, String, hs)
  +L2 = Lb2(hs, c, cs)
  +eqH = LI.revapp(c, hs, cs)
  +eqB = Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, List.reverse(&2, String, z), c <> cs), BD.bts(PT.encs(hs)), hs, hbts)
  +hrP = AB.subst(List<&2, String>, z => {S.report(fa, z, O, N, p) == T : R.Report}, L2, List.append(&2, String, Hs, cs), Equal.sym(List<&2, String>, List.append(&2, String, Hs, cs), L2, eqH), hr)
  +ab = H1.ab_app(rh, [c], PB.and_true_l(E.all_bytes(rh), E.pieces_ok(rh), hby), H1.and_mk2(E.is_bytes(c), True{}, hcb, {==}))
  +po = H1.po_app(rh, [c], PB.and_true_r(E.all_bytes(rh), E.pieces_ok(rh), hby), H1.and_mk2(E.le31(String.length(c)), True{}, hcn, {==}))
  +hbyP = AB.subst(List<&2, String>, z => {E.all_bytes(z) && E.pieces_ok(z) == True{} : Bool}, List.append(&2, String, rh, [c]), Hs,
    Equal.sym(List<&2, String>, Hs, List.append(&2, String, rh, [c]), LI.rg(hs, [c])),
    H1.and_mk2(E.all_bytes(List.append(&2, String, rh, [c])), E.pieces_ok(List.append(&2, String, rh, [c])), ab, po))
  +hbi2 = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, Lb(hs, c, cs), L2, eqB, hbi)
  +hbiP = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, L2, List.append(&2, String, Hs, cs), Equal.sym(List<&2, String>, List.append(&2, String, Hs, cs), L2, eqH), hbi2)
  +eqL = Equal.trans(List<&2, String>, List.append(&2, String, Hs, cs), L2, Lb(hs, c, cs), eqH, Equal.sym(List<&2, String>, Lb(hs, c, cs), L2, eqB))
  +hm1 = Equal.trans(Nat, List.length(&2, String, Hs), Nat.add(List.length(&2, String, hs), 1n), Nat.add(k, 1n), H1.len_rg(hs, [c]),
    Equal.cong(Nat, Nat, z => Nat.add(z, 1n), List.length(&2, String, hs), k, Equal.sym(Nat, k, List.length(&2, String, hs), hk)))
  +ha = AB.subst(Nat, z => {Nat.is_le(Nat.add(1n+Nat.add(z, z), 1n), Nat.add(BD.kx(k), 4n)) == True{} : Bool}, Nat.add(k, 1n), List.length(&2, String, Hs),
    Equal.sym(Nat, List.length(&2, String, Hs), Nat.add(k, 1n), hm1), ar_k1(k))
  PL.plan_bud(dfs, fa, T, cs, O, N, False{}, p, Hs, False{}, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O),
    hb, hm, hst, hg, hrP, hbyP, {==}, hbiP,
    plan_n1(fa, T, cs, O, p, Hs, Lb(hs, c, cs), Nat.add(BD.kx(k), 4n), BN.pick(BD.big(c), 12n), eqL, ha))

law col_if:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, Lb2(hs, c, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  for +hk: {k == List.length(&2, String, hs) : Nat}
  for +hbts: {BD.bts(PT.encs(hs)) == hs : List<&2, String>}
  for +hbi: {BN.biS(S.mkSt(fa, p), Lb(hs, c, cs)) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +b: Bool
  for +hq: {Bool.or(Nat.is_le(W.kmax(), 1n+k), U32.is_lt(U32.from_nat(String.length(c)), W.minp())) == b : Bool}
  API.KontW(dfs, fa, T, W.col.add(b, S.mkSt(fa, p), E.enc(c) <> PT.encs(hs), 1n+k, dfs), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O), O, N)

def col_if(dfs,fa, T, c, cs, O, N, p, hs, k, hb, hm, hst, hg, hr, hby, hk, hbts, hbi, hcb, hcn, b, hq):
  match b:
    case False{}:
      col_more(dfs, fa, T, c, cs, O, N, p, hs, k, hbts, hbi, hcb, hcn,
        big_not_lt(c, hcb, hcn, or_false_r2(Nat.is_le(W.kmax(), 1n+k), U32.is_lt(U32.from_nat(String.length(c)), W.minp()), hq)))
    case True{}:
      %Equal.sym(List<&1, D.Bytes>, W.rev_b(PT.encs(c <> hs), PT.encs(Nil{})), PT.encs(List.reverse.go(&2, String, c <> hs, Nil{})), QB.rev_encs(c <> hs, Nil{})) :
        API.KontW(dfs, fa, T, W.plan(S.mkSt(fa, p), _, False{}, dfs), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O), O, N)
      col_close(dfs, fa, T, c, cs, O, N, p, hs, k, hb, hm, hst, hg, hr, hby, hk, hbts, hbi, hcb, hcn)

# A piece while collecting.
law col_chunk:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, Lb2(hs, c, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  for +hk: {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, p), Lb(hs, c, cs)) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +hdf: {S.StP.dfs(p) == dfs : B.Defs}
  API.KontW(dfs, fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O), O, N)

def col_chunk(dfs,fa, T, c, cs, O, N, p, hs, k, hb, hm, hst, hg, hr, hby, hk, hbi, hcb, hcn, hdf):
  +n1 = BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), c <> cs, False{}, Pr.More{}, O)
  %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
    API.KontW(dfs, fa, T, W.step.q(W.BCol{PT.encs(hs), k}, _, Pr.Chunk{E.enc(c)}), cs, False{}, 0n, n1, O, N)
  %Equal.sym(B.Defs, S.StP.dfs(p), dfs, hdf) :
    API.KontW(dfs, fa, T, W.step.q(W.BCol{PT.encs(hs), k}, (S.mkSt(fa, p), _), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, n1, O, N)
  %Equal.sym(D.Bytes & U32, BY.len(E.enc(c)), (E.enc(c), U32.from_nat(String.length(c))), BNo.len_enc(c)) :
    API.KontW(dfs, fa, T, W.col.len(_, S.mkSt(fa, p), PT.encs(hs), k, dfs), cs, False{}, 0n, n1, O, N)
  col_if(dfs, fa, T, c, cs, O, N, p, hs, k, hb, hm, hst, hg, hr, hby, PB.eq_sound(k, List.length(&2, String, hs), hk), LI.bts_rev(hs, hby), hbi, hcb, hcn,
    Bool.or(Nat.is_le(W.kmax(), 1n+k), U32.is_lt(U32.from_nat(String.length(c)), W.minp())), {==})


# The end of the file while collecting: the batch closes.
law col_eof:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, List.reverse(&2, String, hs), Nil{}), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  for +hk: {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs))), Nil{})) == True{} : Bool}
  for +hdf: {S.StP.dfs(p) == dfs : B.Defs}
  API.KontW(dfs, fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), Pr.Eof{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), Nil{}, False{}, Pr.More{}, O), O, N)

def col_eof(dfs,fa, T, O, N, p, hs, k, hb, hm, hst, hg, hr, hby, hk, hbi, hdf):
  +Hs = List.reverse.go(&2, String, hs, Nil{})
  +n1 = BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), Nil{}, False{}, Pr.More{}, O)
  %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
    API.KontW(dfs, fa, T, W.step.q(W.BCol{PT.encs(hs), k}, _, Pr.Eof{}), Nil{}, True{}, 0n, n1, O, N)
  %Equal.sym(B.Defs, S.StP.dfs(p), dfs, hdf) :
    API.KontW(dfs, fa, T, W.step.q(W.BCol{PT.encs(hs), k}, (S.mkSt(fa, p), _), Pr.Eof{}), Nil{}, True{}, 0n, n1, O, N)
  +hbts = LI.bts_rev(hs, hby)
  +eqB = Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, List.reverse(&2, String, z), Nil{}), BD.bts(PT.encs(hs)), hs, hbts)
  +hbiP = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs))), Nil{}), List.append(&2, String, Hs, Nil{}), eqB, hbi)
  +kk = PB.eq_sound(k, List.length(&2, String, hs), hk)
  +hm1 = Equal.trans(Nat, List.length(&2, String, Hs), Nat.add(List.length(&2, String, hs), 0n), k, H1.len_rg(hs, Nil{}),
    Equal.trans(Nat, Nat.add(List.length(&2, String, hs), 0n), List.length(&2, String, hs), k, N.add_zero(List.length(&2, String, hs)), Equal.sym(Nat, k, List.length(&2, String, hs), kk)))
  +ha = AB.subst(Nat, z => {Nat.is_le(Nat.add(1n+Nat.add(z, z), 1n), Nat.add(BD.kx(k), 4n)) == True{} : Bool}, k, List.length(&2, String, Hs), Equal.sym(Nat, List.length(&2, String, Hs), k, hm1), ar_k0(k))
  %Equal.sym(List<&1, D.Bytes>, W.rev_b(PT.encs(hs), PT.encs(Nil{})), PT.encs(Hs), QB.rev_encs(hs, Nil{})) :
    API.KontW(dfs, fa, T, W.plan(S.mkSt(fa, p), _, True{}, dfs), Nil{}, True{}, 0n, n1, O, N)
  PL.plan_bud(dfs, fa, T, Nil{}, O, N, True{}, p, Hs, True{}, n1, hb, hm, hst, hg, hr, hby, ({==}, {==}), hbiP,
    plan_n1(fa, T, Nil{}, O, p, Hs, List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs))), Nil{}), Nat.add(BD.kx(k), 4n), 0n,
      Equal.sym(List<&2, String>, List.append(&2, String, List.reverse(&2, String, BD.bts(PT.encs(hs))), Nil{}), List.append(&2, String, Hs, Nil{}), eqB), ha))


# The answers
# ===========

# ((V0 + 1) + X) + (R + 1) == ((V0 + (1 + R)) + 1) + X.
law ar_t:
  for +V0: Nat
  for +X: Nat
  for +R: Nat
  {Nat.add(Nat.add(Nat.add(V0, 1n), X), Nat.add(R, 1n)) == Nat.add(Nat.add(Nat.add(V0, 1n+R), 1n), X) : Nat}

def ar_t(V0, X, R):
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(V0, 1n), X), Nat.add(R, 1n)), Nat.add(Nat.add(V0, 1n), Nat.add(X, Nat.add(R, 1n))), Nat.add(V0, Nat.add(1n, Nat.add(X, Nat.add(R, 1n)))),
    N.add_assoc(Nat.add(V0, 1n), X, Nat.add(R, 1n)), N.add_assoc(V0, 1n, Nat.add(X, Nat.add(R, 1n))))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(V0, 1n+R), 1n), X), Nat.add(Nat.add(V0, 1n+R), Nat.add(1n, X)), Nat.add(V0, Nat.add(1n+R, Nat.add(1n, X))),
    N.add_assoc(Nat.add(V0, 1n+R), 1n, X), N.add_assoc(V0, 1n+R, Nat.add(1n, X)))
  +e3 = Equal.trans(Nat, Nat.add(X, Nat.add(R, 1n)), Nat.add(X, 1n+R), 1n+Nat.add(R, X),
    Equal.cong(Nat, Nat, z => Nat.add(X, z), Nat.add(R, 1n), 1n+R, N.add_one(R)),
    Equal.trans(Nat, Nat.add(X, 1n+R), 1n+Nat.add(X, R), 1n+Nat.add(R, X), N.add_succ(X, R),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(X, R), Nat.add(R, X), N.add_comm(X, R))))
  +e4 = Equal.sym(Nat, Nat.add(R, 1n+X), 1n+Nat.add(R, X), N.add_succ(R, X))
  +e5 = Equal.cong(Nat, Nat, z => Nat.add(V0, 1n+z), Nat.add(X, Nat.add(R, 1n)), Nat.add(R, 1n+X), Equal.trans(Nat, Nat.add(X, Nat.add(R, 1n)), 1n+Nat.add(R, X), Nat.add(R, 1n+X), e3, e4))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(V0, 1n), X), Nat.add(R, 1n)), Nat.add(V0, 1n+Nat.add(R, 1n+X)), Nat.add(Nat.add(Nat.add(V0, 1n+R), 1n), X),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(V0, 1n), X), Nat.add(R, 1n)), Nat.add(V0, Nat.add(1n, Nat.add(X, Nat.add(R, 1n)))), Nat.add(V0, 1n+Nat.add(R, 1n+X)), e1, e5),
    Equal.sym(Nat, Nat.add(Nat.add(Nat.add(V0, 1n+R), 1n), X), Nat.add(V0, 1n+Nat.add(R, 1n+X)), e2))

# The plan's Ask answered: the tasks run, the combine starts.
law ask_ref:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +ef: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for d: PT.PcsOK(ps, cs) & PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, BD.plts(PT.mkPls(ps)), cs)) == True{} : Bool}
  for +hdf: {S.StP.dfs(p) == dfs : B.Defs}
  API.KontW(dfs, fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Ref{M.truths(fa, PT.reqs_of(ps))}), cs, ef, List.length(&2, Pr.Req, PT.reqs_of(ps)), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), cs, ef, Pr.Ask{PT.reqs_of(ps)}, O), O, N)

def ask_ref(dfs,fa, T, cs, O, N, p, ps, e, ef, hb, hm, hst, hg, hr, hby, d, he, hbi, hdf):
  +R = List.length(&2, Pr.Req, PT.reqs_of(ps))
  +L = List.append(&2, String, PT.texts(ps), cs)
  +Lp = List.append(&2, String, BD.plts(PT.mkPls(ps)), cs)
  +n1 = BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), cs, ef, Pr.Ask{PT.reqs_of(ps)}, O)
  %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
    API.KontW(dfs, fa, T, W.step.q(W.BAsk{PT.mkPls(ps), e}, _, Pr.Ref{M.truths(fa, PT.reqs_of(ps))}), cs, ef, R, n1, O, N)
  %Equal.sym(B.Defs, S.StP.dfs(p), dfs, hdf) :
    API.KontW(dfs, fa, T, W.step.q(W.BAsk{PT.mkPls(ps), e}, (S.mkSt(fa, p), _), Pr.Ref{M.truths(fa, PT.reqs_of(ps))}), cs, ef, R, n1, O, N)
  +hpl = LI.plts_mk(ps, PB.and_true_l(E.all_bytes(PT.texts(ps)), E.pieces_ok(PT.texts(ps)), hby), PB.and_true_r(E.all_bytes(PT.texts(ps)), E.pieces_ok(PT.texts(ps)), hby))
  +eL = Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, cs), BD.plts(PT.mkPls(ps)), PT.texts(ps), hpl)
  +hbi2 = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, Lp, L, eL, hbi)
  +A = Nat.add(List.length(&2, String, L), 1n)
  +h0 = BNo.ar_r(A, BN.HO(T, O), BDs.WP(fa, L, p), R, BD.XK(cs))
  +hv = AB.subst(List<&2, String>, z => {Nat.is_le(Nat.add(PL.VC(fa, T, cs, O, p, ps), Nat.add(R, 1n)), Nat.add(ST.VQ(T, z, False{}, O, Nat.add(1n+R, BDs.WP(fa, z, p))), BD.XK(cs))) == True{} : Bool},
    L, Lp, Equal.sym(List<&2, String>, Lp, L, eL), h0)
  %QB.opts_mk(fa, p) : API.KontW(dfs, fa, T, W.ask.run(_, PT.mkPls(ps), M.truths(fa, PT.reqs_of(ps)), e, dfs), cs, ef, R, n1, O, N)
  PL.run_tasks(dfs, fa, T, cs, O, N, ef, p, ps, e, R, n1, hb, hm, hst, hg, hr, hby, d, he, hbi2, hv)


# The combine's Ask{[]} answered: the next piece.
law combf_ref:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +e: Bool
  for +ef: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for d: PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs) & PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, BD.tots(PT.mkTOuts(fa, ps, xs)), cs)) == True{} : Bool}
  API.KontW(dfs, fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Ref{M.truths(fa, Nil{})}), cs, ef, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), cs, ef, Pr.Ask{Nil{}}, O), O, N)

def combf_ref(dfs,fa, T, cs, O, N, p, ps, xs, e, ef, hb, hm, hst, hg, hr, hby, hps, d, he, hbi):
  (h1, h2) = d
  %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
    API.KontW(dfs, fa, T, W.step.q(W.BComb{PT.mkTOuts(fa, ps, xs), e, False{}}, _, Pr.Ref{M.truths(fa, Nil{})}), cs, ef, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), cs, ef, Pr.Ask{Nil{}}, O), O, N)
  +hts = LI.tots_mk(dfs, fa, S.StP.o(p), ps, xs, cs, h1)
  +L = List.append(&2, String, PT.texts(ps), cs)
  +Lt = List.append(&2, String, BD.tots(PT.mkTOuts(fa, ps, xs)), cs)
  +eL = Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, cs), BD.tots(PT.mkTOuts(fa, ps, xs)), PT.texts(ps), hts)
  +hbi2 = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, Lt, L, eL, hbi)
  +A = Nat.add(List.length(&2, String, L), 1n)
  +Q2 = Nat.add(A, Nat.add(2n, Nat.add(BN.HO(T, O), Nat.add(1n, BDs.WP(fa, L, p)))))
  +h0 = BNo.ar_r(A, BN.HO(T, O), BDs.WP(fa, L, p), 0n, BD.XK(cs))
  +h1b = AB.subst(Nat, z => {Nat.is_le(Nat.add(PL.VC(fa, T, cs, O, p, ps), Nat.add(0n, 1n)), Nat.add(z, BD.XK(cs))) == True{} : Bool}, Q2, Nat.add(Q2, 0n), Equal.sym(Nat, Nat.add(Q2, 0n), Q2, N.add_zero(Q2)), h0)
  +hv = AB.subst(List<&2, String>, z => {Nat.is_le(Nat.add(PL.VC(fa, T, cs, O, p, ps), Nat.add(0n, 1n)), Nat.add(Nat.add(ST.VQ(T, z, False{}, O, Nat.add(1n, BDs.WP(fa, z, p))), 0n), BD.XK(cs))) == True{} : Bool},
    L, Lt, Equal.sym(List<&2, String>, Lt, L, eL), h1b)
  ST.kont_of(dfs, fa, T, W.comb.next(PT.mkTOuts(fa, ps, xs), S.mkSt(fa, p), e), cs, ef, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), cs, ef, Pr.Ask{Nil{}}, O), PL.VC(fa, T, cs, O, p, ps), O, N,
    CB.comb_bud(dfs, fa, T, cs, O, N, ef, p, ps, xs, e, hb, hm, hst, hg, hr, hby, hps, h2, he, hbi2), hv)


# Q's own Ask in the middle of a piece answered.
law combt_ref:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +e: Bool
  for +rs: List<&2, Pr.Req>
  for +ef: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hask: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
  for +hq: {E.reqs_ok(rs) == True{} : Bool}
  for +hrq: {rs == S.rq(rs) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for hbo: PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, BD.tots(PT.mkTOuts(fa, ps, xs)), cs)) == True{} : Bool}
  API.KontW(dfs, fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Pr.Ref{M.truths(fa, rs)}), cs, ef, List.length(&2, Pr.Req, rs), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), cs, ef, Pr.Ask{rs}, O), O, N)

def combt_ref(dfs,fa, T, cs, O, N, p, ps, xs, e, rs, ef, hb, hw, hask, hq, hrq, hmr, hg, hr, hbo, he, hbi):
  %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
    API.KontW(dfs, fa, T, W.step.q(W.BComb{PT.mkTOuts(fa, ps, xs), e, True{}}, _, Pr.Ref{M.truths(fa, rs)}), cs, ef, List.length(&2, Pr.Req, rs), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), cs, ef, Pr.Ask{rs}, O), O, N)
  +hts = LI.tots_mk(dfs, fa, S.StP.o(p), ps, xs, cs, hbo)
  +L = List.append(&2, String, PT.texts(ps), cs)
  +Lt = List.append(&2, String, BD.tots(PT.mkTOuts(fa, ps, xs)), cs)
  +R = List.length(&2, Pr.Req, rs)
  +W0 = BDs.WP(fa, L, p)
  +X = BD.XK(cs)
  +V0 = ST.VQ(T, L, False{}, O, W0)
  +V = Nat.add(Nat.add(V0, 1n), X)
  +eL = Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, cs), BD.tots(PT.mkTOuts(fa, ps, xs)), PT.texts(ps), hts)
  +hbi2 = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, Lt, L, eL, hbi)
  +h0 = AB.subst(Nat, z => {Nat.is_le(Nat.add(V, Nat.add(R, 1n)), Nat.add(Nat.add(z, 1n), X)) == True{} : Bool}, Nat.add(V0, 1n+R), ST.VQ(T, L, False{}, O, Nat.add(1n+R, W0)),
    Equal.sym(Nat, ST.VQ(T, L, False{}, O, Nat.add(1n+R, W0)), Nat.add(V0, 1n+R), H1.vq_shift(T, L, False{}, O, 1n+R, W0)),
    %ar_t(V0, X, R) : {Nat.is_le(Nat.add(V, Nat.add(R, 1n)), _) == True{} : Bool}; N.le_refl(Nat.add(V, Nat.add(R, 1n))))
  +hv = AB.subst(List<&2, String>, z => {Nat.is_le(Nat.add(V, Nat.add(R, 1n)), Nat.add(Nat.add(ST.VQ(T, z, False{}, O, Nat.add(1n+R, BDs.WP(fa, z, p))), 1n), X)) == True{} : Bool},
    L, Lt, Equal.sym(List<&2, String>, Lt, L, eL), h0)
  ST.kont_of(dfs, fa, T, W.seq_out(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), PT.mkTOuts(fa, ps, xs), e), cs, ef, R, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), cs, ef, Pr.Ask{rs}, O), V, O, N,
    SQ.seq_bud(fa, T, cs, ef, O, W0, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), ps, xs, e, hts, he,
      BS.fed_bud(fa, T, L, O, N, W0, Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), hb, BS.ref_fed(fa, T, L, rs, O, N, p, hb, hw, hr, hask, hq, hrq, hmr, hg, hbi2))),
    hv)

