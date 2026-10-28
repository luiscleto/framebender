import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BDs
import ./proof_b_budget_step.bend as BS
import ./proof_base.bend as PB
import ../lawful-bytes/defs.bend as D
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_api.bend as API
import ./proof_e_mach_dup.bend as DU

# Phase E, area E2: what a wrapper step does to the budget, on the machine
# state (as phase B's BudS): bi holds after it, and for what it writes (within
# the report's output) the potential of its state is at most V. The
# assembly's continuation (API.KontW) follows from V + 1 + reads <= need.

# Phase B's needS with WA (and a pending Ask's RD) replaced by a bound W0.
def VQ(+T: R.Report, +L: List<&2, String>, +e: Bool, +O: String, +W0: Nat) -> Nat:
  Nat.add(Nat.add(List.length(&2, String, L), BN.pick(Bool.not(e), 1n)), Nat.add(2n, Nat.add(BN.HO(T, O), W0)))

def is_fin(nx: Pr.Next) -> Bool:
  match nx:
    case Pr.Finish{c}:
      True{}
    case _:
      False{}

def BudC(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +ef: Bool, +O: String, +V: Nat, s: W.Step) -> Type:
  {BD.biW(BD.sstW(s), cs) == True{} : Bool}
  & (@t: String -> {BD.soutW(s) == Some{t} : Maybe<&2, String>} -> {Nat.is_le(String.length(String.append(O, t)), String.length(R.Report.out(T))) == True{} : Bool}
    -> @n: Nat -> {BD.needW(fa, T, BD.sstW(s), cs, ef, BD.snxW(s), String.append(O, t)) == n : Nat} -> {Nat.is_le(n, V) == True{} : Bool})

def BudW(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +ef: Bool, +O: String, +V: Nat, s: W.Step) -> Type:
  {is_fin(BD.snxW(s)) == False{} : Bool} -> BudC(fa, T, cs, ef, O, V, s)

# ---------------------------------------------------------------------------
# From BudW to the assembly's continuation
# ---------------------------------------------------------------------------

law hop_inv:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +nx: Pr.Next
  for +ef: Bool
  for h: WD.InvW(fa, T, cs, O, N, x, nx, ef)
  {Nat.is_le(String.length(O), String.length(R.Report.out(T))) == True{} : Bool}

def hop_inv(fa, T, cs, O, N, x, nx, ef, h):
  match x:
    case WD.WPic{+p, +b}:
      (a1, h1) = h
      (a2, h2) = h1
      (a3, h3) = h2
      BS.hop(fa, T, List.append(&2, String, WD.held(b), cs), O, N, p, a3, a2)

law nofin_ph:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +p: S.StP
  for +b: WD.BatP
  for +nx: Pr.Next
  for +ef: Bool
  for h: WD.PhaseOK(fa, cs, p, b, nx, ef)
  {is_fin(nx) == False{} : Bool}

def nofin_ph(fa, cs, p, b, nx, ef, h):
  match b nx:
    case _ Pr.More{}:
      {==}
    case _ Pr.Ask{+rs}:
      {==}
    case WD.BNoneP{} Pr.Finish{+c}:
      Empty.absurd({is_fin(Pr.Finish{c}) == False{} : Bool}, h)
    case WD.BColP{+hs, +k} Pr.Finish{+c}:
      (h1, h2) = h
      Empty.absurd({is_fin(Pr.Finish{c}) == False{} : Bool}, PB.true_ne_false(Equal.cong(Pr.Next, Bool, z => is_fin(z), Pr.Finish{c}, Pr.More{}, h1)))
    case WD.BAskP{+ps, +e} Pr.Finish{+c}:
      (h1, h2) = h
      Empty.absurd({is_fin(Pr.Finish{c}) == False{} : Bool}, PB.true_ne_false(Equal.cong(Pr.Next, Bool, z => is_fin(z), Pr.Finish{c}, Pr.Ask{PT.reqs_of(ps)}, h1)))
    case WD.BCombP{+ps, +xs, +e, False{}} Pr.Finish{+c}:
      (h1, h2) = h
      Empty.absurd({is_fin(Pr.Finish{c}) == False{} : Bool}, PB.true_ne_false(Equal.cong(Pr.Next, Bool, z => is_fin(z), Pr.Finish{c}, Pr.Ask{Nil{}}, h1)))
    case WD.BCombP{+ps, +xs, +e, True{}} Pr.Finish{+c}:
      (h1, h2) = h
      Empty.absurd({is_fin(Pr.Finish{c}) == False{} : Bool}, h1)

law inv_nofin:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +nx: Pr.Next
  for +ef: Bool
  for h: WD.InvW(fa, T, cs, O, N, x, nx, ef)
  {is_fin(nx) == False{} : Bool}

def inv_nofin(fa, T, cs, O, N, x, nx, ef, h):
  match x:
    case WD.WPic{+p, +b}:
      (a1, h1) = h
      (a2, h2) = h1
      (a3, h3) = h2
      nofin_ph(fa, cs, p, b, nx, ef, h3)

def need_of(+fa: List<&2, B.Contig>, +T: R.Report, p: W.St & Pr.Next, +cs: List<&2, String>, +ef: Bool, +O: String) -> Nat:
  (st, +nx) = p
  BD.needW(fa, T, st, cs, ef, nx, O)

law kont_k2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for -s: W.Step
  for +cs2: List<&2, String>
  for +de2: Bool
  for +R: Nat
  for +n1: Nat
  for +V: Nat
  for +O: String
  for +N2: List<&2, B.Note>
  for +x2: WD.WPic
  for +nx2: Pr.Next
  for +t: String
  for +hv: {Nat.is_le(Nat.add(V, Nat.add(R, 1n)), n1) == True{} : Bool}
  for +est: {BD.sstW(s) == WD.mkWSt(fa, x2) : W.St}
  for +hnx: {BD.snxW(s) == nx2 : Pr.Next}
  for +hout: {BD.soutW(s) == Some{t} : Maybe<&2, String>}
  for bw: {BD.biW(BD.sstW(s), cs2) == True{} : Bool} & (@t: String -> {BD.soutW(s) == Some{t} : Maybe<&2, String>} -> {Nat.is_le(String.length(String.append(O, t)), String.length(R.Report.out(T))) == True{} : Bool} -> @n: Nat -> {BD.needW(fa, T, BD.sstW(s), cs2, de2, BD.snxW(s), String.append(O, t)) == n : Nat} -> {Nat.is_le(n, V) == True{} : Bool})
  for i1: WD.InvW(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2)
  for i2: WD.InvW(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2)
  WD.InvW(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2) & ({BD.biW(WD.mkWSt(fa, x2), cs2) == True{} : Bool}
    & {Nat.is_le(Nat.add(BD.needW(fa, T, WD.mkWSt(fa, x2), cs2, de2, nx2, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool})

def kont_k2(fa, T, s, cs2, de2, R, n1, V, O, N2, x2, nx2, t, hv, est, hnx, hout, bw, i1, i2):
  (hbi, k) = bw
  +hp = hop_inv(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2, i2)
  +nw = BD.needW(fa, T, WD.mkWSt(fa, x2), cs2, de2, nx2, String.append(O, t))
  +enw = Equal.trans(W.St & Pr.Next, (BD.sstW(s), BD.snxW(s)), (WD.mkWSt(fa, x2), BD.snxW(s)), (WD.mkWSt(fa, x2), nx2),
    Equal.cong(W.St, W.St & Pr.Next, z => (z, BD.snxW(s)), BD.sstW(s), WD.mkWSt(fa, x2), est),
    Equal.cong(Pr.Next, W.St & Pr.Next, z => (WD.mkWSt(fa, x2), z), BD.snxW(s), nx2, hnx))
  +le2 = k(t, hout, hp, nw, Equal.cong(W.St & Pr.Next, Nat, z => need_of(fa, T, z, cs2, de2, String.append(O, t)), (BD.sstW(s), BD.snxW(s)), (WD.mkWSt(fa, x2), nx2), enw))
  (i1, (AB.subst(W.St, z => {BD.biW(z, cs2) == True{} : Bool}, BD.sstW(s), WD.mkWSt(fa, x2), est, hbi),
    N.le_trans(Nat.add(nw, Nat.add(R, 1n)), Nat.add(V, Nat.add(R, 1n)), n1, N.le_add_mono_r(Nat.add(R, 1n), nw, V, le2), hv)))

law kont_k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for -s: W.Step
  for +cs2: List<&2, String>
  for +de2: Bool
  for +R: Nat
  for +n1: Nat
  for +V: Nat
  for +O: String
  for +N2: List<&2, B.Note>
  for +x2: WD.WPic
  for +nx2: Pr.Next
  for +t: String
  for +hv: {Nat.is_le(Nat.add(V, Nat.add(R, 1n)), n1) == True{} : Bool}
  for +est: {BD.sstW(s) == WD.mkWSt(fa, x2) : W.St}
  for +hnx: {BD.snxW(s) == nx2 : Pr.Next}
  for +hout: {BD.soutW(s) == Some{t} : Maybe<&2, String>}
  for bw: BudW(fa, T, cs2, de2, O, V, s)
  for d: WD.InvW(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2) & (WD.InvW(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2) & WD.InvW(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2))
  WD.InvW(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2) & ({BD.biW(WD.mkWSt(fa, x2), cs2) == True{} : Bool}
    & {Nat.is_le(Nat.add(BD.needW(fa, T, WD.mkWSt(fa, x2), cs2, de2, nx2, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool})

def kont_k(fa, T, s, cs2, de2, R, n1, V, O, N2, x2, nx2, t, hv, est, hnx, hout, bw, d):
  (i1, d2) = d
  (i2, i3) = d2
  kont_k2(fa, T, s, cs2, de2, R, n1, V, O, N2, x2, nx2, t, hv, est, hnx, hout,
    bw(AB.subst(Pr.Next, z => {is_fin(z) == False{} : Bool}, nx2, BD.snxW(s), Equal.sym(Pr.Next, BD.snxW(s), nx2, hnx), inv_nofin(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2, i3))),
    i1, i2)

law kont_of:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for -s: W.Step
  for +cs2: List<&2, String>
  for +de2: Bool
  for +R: Nat
  for +n1: Nat
  for +V: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for bw: BudW(fa, T, cs2, de2, O, V, s)
  for +hv: {Nat.is_le(Nat.add(V, Nat.add(R, 1n)), n1) == True{} : Bool}
  API.KontW(fa, T, s, cs2, de2, R, n1, O, N)

def kont_of(fa, T, s, cs2, de2, R, n1, V, O, N, bw, hv):
  +x2 => +nx2 => +t => +N2 => hn2 => +est => +hnx => +hout => inv =>
    kont_k(fa, T, s, cs2, de2, R, n1, V, O, N2, x2, nx2, t, hv, est, hnx, hout, bw,
      DU.inv_dup3(fa, T, cs2, String.append(O, t), N2, x2, nx2, de2, inv))

# ---------------------------------------------------------------------------
# A step of Q, as the wrapper hands it out
# ---------------------------------------------------------------------------

# Phase B's BudS bounds needS by VQ: (a + (2 + X)) <= (a + (2 + Y)) for X <= Y.
law vq_le:
  for +a: Nat
  for +X: Nat
  for +Y: Nat
  for +h: {Nat.is_le(X, Y) == True{} : Bool}
  {Nat.is_le(Nat.add(a, Nat.add(2n, X)), Nat.add(a, Nat.add(2n, Y))) == True{} : Bool}

def vq_le(a, X, Y, h):
  N.le_add_mono_l(a, Nat.add(2n, X), Nat.add(2n, Y), N.le_add_mono_l(2n, X, Y, h))

# A value, named.
def name_was(+fa: List<&2, B.Contig>, st: Norm.St, +cs: List<&2, String>) -> &w: Nat -> {BN.WAS(fa, st, cs) == w : Nat}:
  (BN.WAS(fa, st, cs), {==})

# An equality whose left side is erased, twice.
def eq2(-a: Nat, +b: Nat, e: {a == b : Nat}) -> {a == b : Nat} & {a == b : Nat}:
  %Equal.sym(Nat, a, b, e) : {_ == b : Nat} & {_ == b : Nat}
  ({==}, {==})

# The step's needS within VQ, from BudS's inequality at w = WA(st), with
# what the wrapper adds (X, or X1 then X2).
def needs_le.k(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +e: Bool, +O: String, +W0: Nat, -st: Norm.St, +nx: Pr.Next, +O2: String, +X1: Nat, +X2: Nat, +w: Nat,
  k: @r: Nat -> {BN.RD(nx) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  d: {BN.WAS(fa, st, L) == w : Nat} & {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, st, L, e, nx, O2), X1), X2), Nat.add(Nat.add(VQ(T, L, e, O, W0), X1), X2)) == True{} : Bool}:
  (e1, e2) = d
  +a = Nat.add(List.length(&2, String, L), BN.pick(Bool.not(e), 1n))
  %Equal.sym(Nat, BN.WAS(fa, st, L), w, e1) : {Nat.is_le(Nat.add(Nat.add(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), _)))), X1), X2), Nat.add(Nat.add(VQ(T, L, e, O, W0), X1), X2)) == True{} : Bool}
  N.le_add_mono_r(X2, Nat.add(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), w)))), X1), Nat.add(VQ(T, L, e, O, W0), X1),
    N.le_add_mono_r(X1, Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), w)))), VQ(T, L, e, O, W0),
      vq_le(a, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), w)), Nat.add(BN.HO(T, O), W0), k(BN.RD(nx), {==}, w, e2))))

def needs_le2(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +e: Bool, +O: String, +W0: Nat, -st: Norm.St, +nx: Pr.Next, +O2: String, +X1: Nat, +X2: Nat,
  k: @r: Nat -> {BN.RD(nx) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  ww: &w: Nat -> {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, st, L, e, nx, O2), X1), X2), Nat.add(Nat.add(VQ(T, L, e, O, W0), X1), X2)) == True{} : Bool}:
  (+w, ew) = ww
  needs_le.k(fa, T, L, e, O, W0, st, nx, O2, X1, X2, w, k, eq2(BN.WAS(fa, st, L), w, ew))

# One added term.
def needs_le1.k(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +e: Bool, +O: String, +W0: Nat, -st: Norm.St, +nx: Pr.Next, +O2: String, +X: Nat, +w: Nat,
  k: @r: Nat -> {BN.RD(nx) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  d: {BN.WAS(fa, st, L) == w : Nat} & {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(BN.needS(fa, T, st, L, e, nx, O2), X), Nat.add(VQ(T, L, e, O, W0), X)) == True{} : Bool}:
  (e1, e2) = d
  +a = Nat.add(List.length(&2, String, L), BN.pick(Bool.not(e), 1n))
  %Equal.sym(Nat, BN.WAS(fa, st, L), w, e1) : {Nat.is_le(Nat.add(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), _)))), X), Nat.add(VQ(T, L, e, O, W0), X)) == True{} : Bool}
  N.le_add_mono_r(X, Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), w)))), VQ(T, L, e, O, W0),
    vq_le(a, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), w)), Nat.add(BN.HO(T, O), W0), k(BN.RD(nx), {==}, w, e2)))

def needs_le(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +e: Bool, +O: String, +W0: Nat, -st: Norm.St, +nx: Pr.Next, +O2: String, +X: Nat,
  k: @r: Nat -> {BN.RD(nx) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  ww: &w: Nat -> {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(BN.needS(fa, T, st, L, e, nx, O2), X), Nat.add(VQ(T, L, e, O, W0), X)) == True{} : Bool}:
  (+w, ew) = ww
  needs_le1.k(fa, T, L, e, O, W0, st, nx, O2, X, w, k, eq2(BN.WAS(fa, st, L), w, ew))

# With no batch after it.
law wrap_none:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +ef: Bool
  for +O: String
  for +W0: Nat
  for s: Norm.Step
  for h: BDs.BudS(fa, T, cs, O, W0, s)
  BudW(fa, T, cs, ef, O, Nat.add(VQ(T, cs, ef, O, W0), BD.XK(cs)), W.wrap(s, W.BNone{}))

def wrap_none(fa, T, cs, ef, O, W0, s, h):
  match s:
    case Norm.Step{st, b, +ns, +nx}:
      (hbi, k) = h
      hnf => (hbi, +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(VQ(T, cs, ef, O, W0), BD.XK(cs))) == True{} : Bool};
        needs_le(fa, T, cs, ef, O, W0, st, nx, String.append(O, t), BD.XK(cs), k(t, hout, hp), name_was(fa, st, cs)))

# A larger bound.
law budw_mono.k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +ef: Bool
  for +O: String
  for +V1: Nat
  for +V2: Nat
  for -s: W.Step
  for c: {BD.biW(BD.sstW(s), cs) == True{} : Bool} & (@t: String -> {BD.soutW(s) == Some{t} : Maybe<&2, String>} -> {Nat.is_le(String.length(String.append(O, t)), String.length(R.Report.out(T))) == True{} : Bool} -> @n: Nat -> {BD.needW(fa, T, BD.sstW(s), cs, ef, BD.snxW(s), String.append(O, t)) == n : Nat} -> {Nat.is_le(n, V1) == True{} : Bool})
  for +h: {Nat.is_le(V1, V2) == True{} : Bool}
  {BD.biW(BD.sstW(s), cs) == True{} : Bool} & (@t: String -> {BD.soutW(s) == Some{t} : Maybe<&2, String>} -> {Nat.is_le(String.length(String.append(O, t)), String.length(R.Report.out(T))) == True{} : Bool} -> @n: Nat -> {BD.needW(fa, T, BD.sstW(s), cs, ef, BD.snxW(s), String.append(O, t)) == n : Nat} -> {Nat.is_le(n, V2) == True{} : Bool})

def budw_mono.k(fa, T, cs, ef, O, V1, V2, s, c, h):
  (hbi, k) = c
  (hbi, +t => hout => hp => +n => en => N.le_trans(n, V1, V2, k(t, hout, hp, n, en), h))

law budw_mono:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +ef: Bool
  for +O: String
  for +V1: Nat
  for +V2: Nat
  for -s: W.Step
  for bw: BudW(fa, T, cs, ef, O, V1, s)
  for +h: {Nat.is_le(V1, V2) == True{} : Bool}
  BudW(fa, T, cs, ef, O, V2, s)

def budw_mono(fa, T, cs, ef, O, V1, V2, s, bw, h):
  hnf => budw_mono.k(fa, T, cs, ef, O, V1, V2, s, bw(hnf), h)
