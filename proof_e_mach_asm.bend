import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_cachedefs.bend as PC
import ./proof_b_drivedefs.bend as DD
import ./proof_base.bend as PB
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-bytes@0.1.1.0/defs.bend as D
import ./proof_b_fa_bytes.bend as FB
import ./proof_b_assemble.bend as AS
import ./proof_b_budget_need.bend as BN
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap.bend as WS
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_api.bend as API
import ./proof_e_bud_main.bend as BM
import ./proof_e_mach_inv.bend as IV
import ./proof_e_mach_dup.bend as DU

# Phase E, area E2: the law machine for the parallel machine, assembled as
# proof_b_assemble.bend's: the driver (proof_e_mdefs.bend's copy of
# MACHINE.bend's drive, dstep, absorb, result) keeps an invariant Good: the
# machine's state is pictured by a good x (E1's InvW) standing for the report
# T with what the driver collected, and reads + need <= the bound, need <=
# the fuel left (the budget, proof_e_bud_api.bend). Each driver step (E1's
# wstep_*) keeps Good with one less fuel, so drive reaches the stopped state
# with the report.

def txt(+cs: List<&2, String>) -> Bool:
  API.txt(cs)

def NW(+fa: List<&2, B.Contig>, +T: R.Report, +x: WD.WPic, +cs: List<&2, String>, +de: Bool, +nx: Pr.Next, +O: String) -> Nat:
  BD.needW(fa, T, WD.mkWSt(fa, x), cs, de, nx, O)

def GoodN(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, st: W.St, nx: Pr.Next, +dcs: List<&2, String>, +de: Bool, +rd: Nat, +g: Bool, +out: String, +notes: List<&2, B.Note>) -> Type:
  match nx:
    case Pr.Finish{c}:
      {g == True{} : Bool} & ({R.Report{out, notes, c} == T : R.Report} & ({Nat.is_le(Nat.add(rd, 1n), lim) == True{} : Bool} & {Nat.is_le(1n, f) == True{} : Bool}))
    case Pr.More{}:
      &x: WD.WPic -> ({st == WD.mkWSt(fa, x) : W.St} & (WD.InvW(dfs, fa, T, dcs, out, notes, x, Pr.More{}, de)
        & ({g == True{} : Bool} & ({txt(dcs) == True{} : Bool} & ({BD.biW(WD.mkWSt(fa, x), dcs) == True{} : Bool}
        & ({Nat.is_le(Nat.add(rd, NW(fa, T, x, dcs, de, Pr.More{}, out)), lim) == True{} : Bool}
        & {Nat.is_le(NW(fa, T, x, dcs, de, Pr.More{}, out), f) == True{} : Bool}))))))
    case Pr.Ask{rs}:
      &x: WD.WPic -> ({st == WD.mkWSt(fa, x) : W.St} & (WD.InvW(dfs, fa, T, dcs, out, notes, x, Pr.Ask{rs}, de)
        & ({g == True{} : Bool} & ({txt(dcs) == True{} : Bool} & ({BD.biW(WD.mkWSt(fa, x), dcs) == True{} : Bool}
        & ({Nat.is_le(Nat.add(rd, NW(fa, T, x, dcs, de, Pr.Ask{rs}, out)), lim) == True{} : Bool}
        & {Nat.is_le(NW(fa, T, x, dcs, de, Pr.Ask{rs}, out), f) == True{} : Bool}))))))

def GoodD(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, st: W.St, +nx: Pr.Next, +dcs: List<&2, String>, +de: Bool, +rd: Nat, +g: Bool, +out: String, +notes: List<&2, B.Note>, done: Maybe<&2, Nat>) -> Type:
  match done:
    case Some{c}:
      {g == True{} : Bool} & ({R.Report{out, notes, c} == T : R.Report} & {Nat.is_le(rd, lim) == True{} : Bool})
    case None{}:
      GoodN(dfs, fa, T, lim, f, st, nx, dcs, de, rd, g, out, notes)

def Good(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, d: M.DSt) -> Type:
  match d:
    case M.DSt{st, nx, dcs, de, rd, g, out, notes, done}:
      GoodD(dfs, fa, T, lim, f, st, nx, dcs, de, rd, g, out, notes, done)

def StepR(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, d: M.DSt) -> Type:
  match f:
    case 0n:
      Empty
    case 1n+h:
      Good(dfs, fa, T, lim, h, d)

# ---------------------------------------------------------------------------
# The driver absorbs a step
# ---------------------------------------------------------------------------

law am_more.k:
  for +dfs: B.Defs
  for +h: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: W.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +t: String
  for +x2: WD.WPic
  for +hfu: {Nat.is_le(n1, 1n+h) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == WD.mkWSt(fa, x2) : W.St}
  for inv: WD.InvW(dfs, fa, T, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.More{}, de2)
  for +bi2: {BD.biW(WD.mkWSt(fa, x2), cs2) == True{} : Bool}
  for +drop: {Nat.is_le(Nat.add(NW(fa, T, x2, cs2, de2, Pr.More{}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool}
  Good(dfs, fa, T, lim, h, M.absorb(W.Step{st2, b, ns, Pr.More{}}, cs2, de2, rd2, G, O, N))

def am_more.k(dfs,h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, t, x2, hfu, eout, est, inv, bi2, drop):
  +n2 = NW(fa, T, x2, cs2, de2, Pr.More{}, String.append(O, t))
  %Equal.sym(Maybe<&2, String>, E.out(b), Some{t}, eout) : Good(dfs, fa, T, lim, h, M.absorb.k(st2, Pr.More{}, cs2, de2, rd2, G, M.absorb.out(_, O), N, ns))
  (x2, (est, (inv, (AS.and_tt(G, hG), (htx, (bi2,
    (%Equal.sym(Nat, rd2, Nat.add(rd, R), hrd) : {Nat.is_le(Nat.add(_, n2), lim) == True{} : Bool}; AS.ar_lim(rd, R, n2, n1, lim, drop, hlim),
    AS.ar_fuel(R, n2, n1, h, drop, hfu))))))))

law am_more.b:
  for +dfs: B.Defs
  for +h: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: W.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +t: String
  for +x2: WD.WPic
  for +hfu: {Nat.is_le(n1, 1n+h) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == WD.mkWSt(fa, x2) : W.St}
  for bud: WD.InvW(dfs, fa, T, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.More{}, de2) & ({BD.biW(WD.mkWSt(fa, x2), cs2) == True{} : Bool} & {Nat.is_le(Nat.add(NW(fa, T, x2, cs2, de2, Pr.More{}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool})
  Good(dfs, fa, T, lim, h, M.absorb(W.Step{st2, b, ns, Pr.More{}}, cs2, de2, rd2, G, O, N))

def am_more.b(dfs,h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, t, x2, hfu, eout, est, bud):
  (inv, b2) = bud
  (bi2, drop) = b2
  am_more.k(dfs, h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, t, x2, hfu, eout, est, inv, bi2, drop)

law am_ask.k:
  for +dfs: B.Defs
  for +h: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: W.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +rs2: List<&2, Pr.Req>
  for +t: String
  for +x2: WD.WPic
  for +hfu: {Nat.is_le(n1, 1n+h) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == WD.mkWSt(fa, x2) : W.St}
  for inv: WD.InvW(dfs, fa, T, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.Ask{rs2}, de2)
  for +bi2: {BD.biW(WD.mkWSt(fa, x2), cs2) == True{} : Bool}
  for +drop: {Nat.is_le(Nat.add(NW(fa, T, x2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool}
  Good(dfs, fa, T, lim, h, M.absorb(W.Step{st2, b, ns, Pr.Ask{rs2}}, cs2, de2, rd2, G, O, N))

def am_ask.k(dfs,h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, rs2, t, x2, hfu, eout, est, inv, bi2, drop):
  +n2 = NW(fa, T, x2, cs2, de2, Pr.Ask{rs2}, String.append(O, t))
  %Equal.sym(Maybe<&2, String>, E.out(b), Some{t}, eout) : Good(dfs, fa, T, lim, h, M.absorb.k(st2, Pr.Ask{rs2}, cs2, de2, rd2, G, M.absorb.out(_, O), N, ns))
  (x2, (est, (inv, (AS.and_tt(G, hG), (htx, (bi2,
    (%Equal.sym(Nat, rd2, Nat.add(rd, R), hrd) : {Nat.is_le(Nat.add(_, n2), lim) == True{} : Bool}; AS.ar_lim(rd, R, n2, n1, lim, drop, hlim),
    AS.ar_fuel(R, n2, n1, h, drop, hfu))))))))

law am_ask.b:
  for +dfs: B.Defs
  for +h: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: W.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +rs2: List<&2, Pr.Req>
  for +t: String
  for +x2: WD.WPic
  for +hfu: {Nat.is_le(n1, 1n+h) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == WD.mkWSt(fa, x2) : W.St}
  for bud: WD.InvW(dfs, fa, T, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.Ask{rs2}, de2) & ({BD.biW(WD.mkWSt(fa, x2), cs2) == True{} : Bool} & {Nat.is_le(Nat.add(NW(fa, T, x2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool})
  Good(dfs, fa, T, lim, h, M.absorb(W.Step{st2, b, ns, Pr.Ask{rs2}}, cs2, de2, rd2, G, O, N))

def am_ask.b(dfs,h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, rs2, t, x2, hfu, eout, est, bud):
  (inv, b2) = bud
  (bi2, drop) = b2
  am_ask.k(dfs, h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, rs2, t, x2, hfu, eout, est, inv, bi2, drop)

# No fuel left is impossible after a drop (the drop given with bi).
law zero_k:
  for +R: Nat
  for +n2: Nat
  for +n1: Nat
  for +B0: Bool
  for -I: Type
  for bud: I & ({B0 == True{} : Bool} & {Nat.is_le(Nat.add(n2, Nat.add(R, 1n)), n1) == True{} : Bool})
  for +hf: {Nat.is_le(n1, 0n) == True{} : Bool}
  Empty

def zero_k(R, n2, n1, B0, I, bud, hf):
  (i, b1) = bud
  (b0, drop) = b1
  AS.ar_zero(R, n2, n1, drop, hf)

# Any step, from E1's guarantee and the budget.
law absorb_ok:
  for +dfs: B.Defs
  for s: W.Step
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(n1, f) == True{} : Bool}
  for sg: WD.StepGW(dfs, fa, T, cs2, O, N, de2, s)
  for kb: API.KontW(dfs, fa, T, s, cs2, de2, R, n1, O, N)
  for kf: API.KFinW(s, R, n1)
  StepR(dfs, fa, T, lim, f, M.absorb(s, cs2, de2, rd2, G, O, N))

def absorb_ok(dfs,s, f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, hfu, sg, kb, kf):
  match s f:
    case W.Step{st2, b, +ns, Pr.More{}} 0n:
      (+t, g1) = sg
      (+x2, g2) = g1
      (+eout, g3) = g2
      (+est, inv) = g3
      zero_k(R, NW(fa, T, x2, cs2, de2, Pr.More{}, String.append(O, t)), n1, BD.biW(WD.mkWSt(fa, x2), cs2), WD.InvW(dfs, fa, T, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.More{}, de2), kb(x2, Pr.More{}, t, List.append(&2, B.Note, N, ns), {==}, est, {==}, eout, inv), hfu)
    case W.Step{st2, b, +ns, Pr.More{}} 1n+h:
      (+t, g1) = sg
      (+x2, g2) = g1
      (+eout, g3) = g2
      (+est, inv) = g3
      am_more.b(dfs, h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, t, x2, hfu, eout, est, kb(x2, Pr.More{}, t, List.append(&2, B.Note, N, ns), {==}, est, {==}, eout, inv))
    case W.Step{st2, b, +ns, Pr.Ask{+rs2}} 0n:
      (+t, g1) = sg
      (+x2, g2) = g1
      (+eout, g3) = g2
      (+est, inv) = g3
      zero_k(R, NW(fa, T, x2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), n1, BD.biW(WD.mkWSt(fa, x2), cs2), WD.InvW(dfs, fa, T, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.Ask{rs2}, de2), kb(x2, Pr.Ask{rs2}, t, List.append(&2, B.Note, N, ns), {==}, est, {==}, eout, inv), hfu)
    case W.Step{st2, b, +ns, Pr.Ask{+rs2}} 1n+h:
      (+t, g1) = sg
      (+x2, g2) = g1
      (+eout, g3) = g2
      (+est, inv) = g3
      am_ask.b(dfs, h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, G, hG, hrd, htx, hlim, st2, b, ns, rs2, t, x2, hfu, eout, est, kb(x2, Pr.Ask{rs2}, t, List.append(&2, B.Note, N, ns), {==}, est, {==}, eout, inv))
    case W.Step{st2, b, ns, Pr.Finish{+c}} 0n:
      AS.ar_zero(R, 1n, n1, AS.fin_drop(R, n1, kf(c, {==})), hfu)
    case W.Step{st2, b, ns, Pr.Finish{+c}} 1n+h:
      (+t, g1) = sg
      (eout, rep) = g1
      +drop = AS.fin_drop(R, n1, kf(c, {==}))
      %Equal.sym(Maybe<&2, String>, E.out(b), Some{t}, eout) : Good(dfs, fa, T, lim, h, M.absorb.k(st2, Pr.Finish{c}, cs2, de2, rd2, G, M.absorb.out(_, O), N, ns))
      (AS.and_tt(G, hG), (rep, (%Equal.sym(Nat, rd2, Nat.add(rd, R), hrd) : {Nat.is_le(Nat.add(_, 1n), lim) == True{} : Bool}; AS.ar_lim(rd, R, 1n, n1, lim, drop, hlim), AS.ar_fuel(R, 1n, n1, h, drop, hfu))))

# ---------------------------------------------------------------------------
# The driver's steps, by kind
# ---------------------------------------------------------------------------

# A piece of the file (More, pieces left).
law k_chunk:
  for +dfs: B.Defs
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: W.St
  for +c: String
  for +ct: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +x: WD.WPic
  for +est: {st == WD.mkWSt(fa, x) : W.St}
  for d: WD.InvW(dfs, fa, T, c <> ct, out, notes, x, Pr.More{}, de) & WD.InvW(dfs, fa, T, c <> ct, out, notes, x, Pr.More{}, de)
  for +hg: {g == True{} : Bool}
  for +htx: {txt(c <> ct) == True{} : Bool}
  for +hbi: {BD.biW(WD.mkWSt(fa, x), c <> ct) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, NW(fa, T, x, c <> ct, de, Pr.More{}, out)), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(NW(fa, T, x, c <> ct, de, Pr.More{}, out), f) == True{} : Bool}
  StepR(dfs, fa, T, lim, f, M.dstep(fa, M.DSt{st, Pr.More{}, c <> ct, de, rd, g, out, notes, None{}}))

def k_chunk(dfs,f, fa, T, lim, hbfa, st, c, ct, de, rd, g, out, notes, x, est, d, hg, htx, hbi, hlim, hfu):
  match de:
    case True{}:
      (i1, i2) = d
      Empty.absurd(StepR(dfs, fa, T, lim, f, M.dstep(fa, M.DSt{st, Pr.More{}, c <> ct, True{}, rd, g, out, notes, None{}})), PB.true_ne_false(IV.inv_more_ef(dfs, fa, T, c <> ct, out, notes, x, True{}, i1)))
    case False{}:
      (i1, i2) = d
      +hA = PB.and_true_l(Bool.and(E.is_bytes(c), E.all_bytes(ct)), Bool.and(E.le31(String.length(c)), E.pieces_ok(ct)), htx)
      +hP = PB.and_true_r(Bool.and(E.is_bytes(c), E.all_bytes(ct)), Bool.and(E.le31(String.length(c)), E.pieces_ok(ct)), htx)
      +hcb = PB.and_true_l(E.is_bytes(c), E.all_bytes(ct), hA)
      +hcn = PB.and_true_l(E.le31(String.length(c)), E.pieces_ok(ct), hP)
      +htx2 = AS.and_mk(E.all_bytes(ct), E.pieces_ok(ct), PB.and_true_r(E.is_bytes(c), E.all_bytes(ct), hA), PB.and_true_r(E.le31(String.length(c)), E.pieces_ok(ct), hP))
      +n1 = NW(fa, T, x, c <> ct, False{}, Pr.More{}, out)
      %Equal.sym(W.St, st, WD.mkWSt(fa, x), est) : StepR(dfs, fa, T, lim, f, M.absorb(W.step(_, Pr.Chunk{E.enc(c)}), ct, False{}, rd, g, out, notes))
      absorb_ok(dfs, W.step(WD.mkWSt(fa, x), Pr.Chunk{E.enc(c)}), f, fa, T, lim, ct, False{}, rd, rd, 0n, n1, out, notes, g, hg,
        Equal.sym(Nat, Nat.add(rd, 0n), rd, N.add_zero(rd)), htx2, hlim, hfu,
        WS.wstep_chunk(dfs, fa, T, c, ct, out, notes, x, hbfa, i1, hcb, hcn, htx2),
        BM.bud_chunkW(dfs, fa, T, c, ct, out, notes, x, hbfa, i2, hbi, htx),
        code => hnx => API.need_ge(fa, T, x, c <> ct, False{}, Pr.More{}, out))

# The end of the file (More, no piece left).
law k_eof:
  for +dfs: B.Defs
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: W.St
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +x: WD.WPic
  for +est: {st == WD.mkWSt(fa, x) : W.St}
  for d: WD.InvW(dfs, fa, T, Nil{}, out, notes, x, Pr.More{}, de) & WD.InvW(dfs, fa, T, Nil{}, out, notes, x, Pr.More{}, de)
  for +hg: {g == True{} : Bool}
  for +hbi: {BD.biW(WD.mkWSt(fa, x), Nil{}) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, NW(fa, T, x, Nil{}, de, Pr.More{}, out)), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(NW(fa, T, x, Nil{}, de, Pr.More{}, out), f) == True{} : Bool}
  StepR(dfs, fa, T, lim, f, M.dstep(fa, M.DSt{st, Pr.More{}, Nil{}, de, rd, g, out, notes, None{}}))

def k_eof(dfs,f, fa, T, lim, hbfa, st, de, rd, g, out, notes, x, est, d, hg, hbi, hlim, hfu):
  match de:
    case True{}:
      (i1, i2) = d
      Empty.absurd(StepR(dfs, fa, T, lim, f, M.dstep(fa, M.DSt{st, Pr.More{}, Nil{}, True{}, rd, g, out, notes, None{}})), PB.true_ne_false(IV.inv_more_ef(dfs, fa, T, Nil{}, out, notes, x, True{}, i1)))
    case False{}:
      (i1, i2) = d
      +n1 = NW(fa, T, x, Nil{}, False{}, Pr.More{}, out)
      %Equal.sym(W.St, st, WD.mkWSt(fa, x), est) : StepR(dfs, fa, T, lim, f, M.absorb(W.step(_, Pr.Eof{}), Nil{}, True{}, rd, g, out, notes))
      absorb_ok(dfs, W.step(WD.mkWSt(fa, x), Pr.Eof{}), f, fa, T, lim, Nil{}, True{}, rd, rd, 0n, n1, out, notes, g, hg,
        Equal.sym(Nat, Nat.add(rd, 0n), rd, N.add_zero(rd)), {==}, hlim, hfu,
        WS.wstep_eof(dfs, fa, T, out, notes, x, hbfa, i1),
        BM.bud_eofW(dfs, fa, T, out, notes, x, hbfa, i2, hbi),
        code => hnx => API.need_ge(fa, T, x, Nil{}, False{}, Pr.More{}, out))

law fin_ref:
  for +R: Nat
  for +n: Nat
  for +h: {Nat.is_le(Nat.add(2n, 1n+R), n) == True{} : Bool}
  {Nat.is_le(Nat.add(R, 2n), n) == True{} : Bool}

def fin_ref(R, n, h):
  %Equal.sym(Nat, Nat.add(R, 2n), Nat.add(2n, R), N.add_comm(R, 2n)) : {Nat.is_le(_, n) == True{} : Bool}
  N.le_trans(Nat.add(2n, R), Nat.add(2n, 1n+R), n, N.le_add_l(Nat.add(2n, R), 1n), h)

# The answers to an Ask.
law k_ask:
  for +dfs: B.Defs
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: W.St
  for +rs: List<&2, Pr.Req>
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +x: WD.WPic
  for +est: {st == WD.mkWSt(fa, x) : W.St}
  for d: WD.InvW(dfs, fa, T, dcs, out, notes, x, Pr.Ask{rs}, de) & (WD.InvW(dfs, fa, T, dcs, out, notes, x, Pr.Ask{rs}, de) & WD.InvW(dfs, fa, T, dcs, out, notes, x, Pr.Ask{rs}, de))
  for +hg: {g == True{} : Bool}
  for +htx: {txt(dcs) == True{} : Bool}
  for +hbi: {BD.biW(WD.mkWSt(fa, x), dcs) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, NW(fa, T, x, dcs, de, Pr.Ask{rs}, out)), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(NW(fa, T, x, dcs, de, Pr.Ask{rs}, out), f) == True{} : Bool}
  StepR(dfs, fa, T, lim, f, M.dstep(fa, M.DSt{st, Pr.Ask{rs}, dcs, de, rd, g, out, notes, None{}}))

def k_ask(dfs,f, fa, T, lim, hbfa, st, rs, dcs, de, rd, g, out, notes, x, est, d, hg, htx, hbi, hlim, hfu):
  (i1, d2) = d
  (i2, i3) = d2
  +n1 = NW(fa, T, x, dcs, de, Pr.Ask{rs}, out)
  +R = List.length(&2, Pr.Req, rs)
  %Equal.sym(W.St, st, WD.mkWSt(fa, x), est) :
    StepR(dfs, fa, T, lim, f, M.absorb(W.step(_, Pr.Ref{M.truths(fa, rs)}), dcs, de, Nat.add(rd, R), Bool.and(g, E.reqs_ok(rs)), out, notes))
  absorb_ok(dfs, W.step(WD.mkWSt(fa, x), Pr.Ref{M.truths(fa, rs)}), f, fa, T, lim, dcs, de, rd, Nat.add(rd, R), R, n1, out, notes,
    Bool.and(g, E.reqs_ok(rs)), AS.and_mk(g, E.reqs_ok(rs), hg, IV.inv_ask_reqs(dfs, fa, T, dcs, out, notes, x, rs, de, i3)), {==}, htx, hlim, hfu,
    WS.wstep_ref(dfs, fa, T, dcs, out, notes, x, rs, de, hbfa, i1, htx),
    BM.bud_refW(dfs, fa, T, dcs, out, notes, x, rs, de, hbfa, i2, hbi, htx),
    code => hnx => fin_ref(R, n1, API.need_ge(fa, T, x, dcs, de, Pr.Ask{rs}, out)))

# The machine said Finish: the driver stops.
law k_fin:
  for +dfs: B.Defs
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for -st: W.St
  for +c: Nat
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +hg: {g == True{} : Bool}
  for +hrep: {R.Report{out, notes, c} == T : R.Report}
  for +hl: {Nat.is_le(Nat.add(rd, 1n), lim) == True{} : Bool}
  for +hf1: {Nat.is_le(1n, f) == True{} : Bool}
  StepR(dfs, fa, T, lim, f, M.dstep(fa, M.DSt{st, Pr.Finish{c}, dcs, de, rd, g, out, notes, None{}}))

def k_fin(dfs,f, fa, T, lim, st, c, dcs, de, rd, g, out, notes, hg, hrep, hl, hf1):
  match f:
    case 0n:
      PB.false_ne_true(hf1)
    case 1n+h:
      (hg, (hrep, AS.le_pred(rd, lim, hl)))

# ---------------------------------------------------------------------------
# The drive
# ---------------------------------------------------------------------------

law step_good:
  for +dfs: B.Defs
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: W.St
  for +nx: Pr.Next
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for gd: Good(dfs, fa, T, lim, f, M.DSt{st, nx, dcs, de, rd, g, out, notes, None{}})
  StepR(dfs, fa, T, lim, f, M.dstep(fa, M.DSt{st, nx, dcs, de, rd, g, out, notes, None{}}))

def step_good(dfs,f, fa, T, lim, hbfa, st, nx, dcs, de, rd, g, out, notes, gd):
  match nx dcs:
    case Pr.Finish{+c} _:
      (hg, g1) = gd
      (hrep, g2) = g1
      (hl, hf1) = g2
      k_fin(dfs, f, fa, T, lim, st, c, dcs, de, rd, g, out, notes, hg, hrep, hl, hf1)
    case Pr.More{} Nil{}:
      (+x, g1) = gd
      (est, g2) = g1
      (inv, g3) = g2
      (hg, g4) = g3
      (htx, g5) = g4
      (hbi, g6) = g5
      (hlim, hfu) = g6
      k_eof(dfs, f, fa, T, lim, hbfa, st, de, rd, g, out, notes, x, est, DU.inv_dup(dfs, fa, T, Nil{}, out, notes, x, Pr.More{}, de, inv), hg, hbi, hlim, hfu)
    case Pr.More{} Con{+c, +ct}:
      (+x, g1) = gd
      (est, g2) = g1
      (inv, g3) = g2
      (hg, g4) = g3
      (htx, g5) = g4
      (hbi, g6) = g5
      (hlim, hfu) = g6
      k_chunk(dfs, f, fa, T, lim, hbfa, st, c, ct, de, rd, g, out, notes, x, est, DU.inv_dup(dfs, fa, T, c <> ct, out, notes, x, Pr.More{}, de, inv), hg, htx, hbi, hlim, hfu)
    case Pr.Ask{+rs} _:
      (+x, g1) = gd
      (est, g2) = g1
      (inv, g3) = g2
      (hg, g4) = g3
      (htx, g5) = g4
      (hbi, g6) = g5
      (hlim, hfu) = g6
      k_ask(dfs, f, fa, T, lim, hbfa, st, rs, dcs, de, rd, g, out, notes, x, est, DU.inv_dup3(dfs, fa, T, dcs, out, notes, x, Pr.Ask{rs}, de, inv), hg, htx, hbi, hlim, hfu)

# A stopped driver stays as it is.
law drive_done:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for -st: W.St
  for +nx: Pr.Next
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +c: Nat
  {M.drive(f, fa, M.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}) == M.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}} : M.DSt}

def drive_done(f, fa, st, nx, dcs, de, rd, g, out, notes, c):
  match f nx:
    case 0n _:
      {==}
    case 1n+h Pr.More{}:
      drive_done(h, fa, st, Pr.More{}, dcs, de, rd, g, out, notes, c)
    case 1n+h Pr.Ask{+rs}:
      drive_done(h, fa, st, Pr.Ask{rs}, dcs, de, rd, g, out, notes, c)
    case 1n+h Pr.Finish{+cc}:
      drive_done(h, fa, st, Pr.Finish{cc}, dcs, de, rd, g, out, notes, c)

law done_res:
  for +dfs: B.Defs
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for -st: W.St
  for +nx: Pr.Next
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +c: Nat
  for gd: Good(dfs, fa, T, lim, f, M.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}})
  {M.result(M.drive(f, fa, M.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}), lim) == Some{T} : Maybe<&2, R.Report>}

def done_res(dfs,f, fa, T, lim, st, nx, dcs, de, rd, g, out, notes, c, gd):
  (hg, g1) = gd
  (hrep, hk) = g1
  %Equal.sym(M.DSt, M.drive(f, fa, M.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}), M.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}, drive_done(f, fa, st, nx, dcs, de, rd, g, out, notes, c)) :
    {M.result(_, lim) == Some{T} : Maybe<&2, R.Report>}
  %Equal.sym(Bool, g, True{}, hg) : {M.result.if(Bool.and(_, Nat.is_le(rd, lim)), R.Report{out, notes, c}) == Some{T} : Maybe<&2, R.Report>}
  %Equal.sym(Bool, Nat.is_le(rd, lim), True{}, hk) : {M.result.if(Bool.and(True{}, _), R.Report{out, notes, c}) == Some{T} : Maybe<&2, R.Report>}
  Equal.cong(R.Report, Maybe<&2, R.Report>, z => Some{z}, R.Report{out, notes, c}, T, hrep)

# The drive ends with the report, given a good state and fuel for it.
law drive_ok:
  for +dfs: B.Defs
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for d: M.DSt
  for gd: Good(dfs, fa, T, lim, f, d)
  {M.result(M.drive(f, fa, d), lim) == Some{T} : Maybe<&2, R.Report>}

def drive_ok(dfs,f, fa, T, lim, hbfa, d, gd):
  match f d:
    case _ M.DSt{st, +nx, +dcs, +de, +rd, +g, +out, +notes, Some{+c}}:
      done_res(dfs, f, fa, T, lim, st, nx, dcs, de, rd, g, out, notes, c, gd)
    case 0n M.DSt{st, +nx, +dcs, +de, +rd, +g, +out, +notes, None{}}:
      Empty.absurd({M.result(M.drive(0n, fa, M.DSt{st, nx, dcs, de, rd, g, out, notes, None{}}), lim) == Some{T} : Maybe<&2, R.Report>},
        step_good(dfs, 0n, fa, T, lim, hbfa, st, nx, dcs, de, rd, g, out, notes, gd))
    case 1n+h M.DSt{st, +nx, +dcs, +de, +rd, +g, +out, +notes, None{}}:
      drive_ok(dfs, h, fa, T, lim, hbfa, M.dstep(fa, M.DSt{st, nx, dcs, de, rd, g, out, notes, None{}}),
        step_good(dfs, 1n+h, fa, T, lim, hbfa, st, nx, dcs, de, rd, g, out, notes, gd))

# ---------------------------------------------------------------------------
# The law machine
# ---------------------------------------------------------------------------

def st0(+dfs: B.Defs, +o: B.Opts, +ref: String, +vcfpath: String) -> W.St:
  W.St{DD.start_st(dfs, Norm.start.of(Some{B.Cfg{o, ref, vcfpath}})), W.BNone{}}

law machine_go:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +x: WD.WPic
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  for +est: {WD.wstart_st(dfs, W.start(argv)) == WD.mkWSt(B.Fasta.parse(fasta), x) : W.St}
  for inv: WD.InvW(dfs, B.Fasta.parse(fasta), R.finish(L.run.go(B.Text.lines(String.concat(cs)), B.Fasta.parse(fasta), dfs, o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{})
  for +hbi0: {BD.biW(W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs) == True{} : Bool}
  for +hn0: {Nat.is_le(BD.needW(B.Fasta.parse(fasta), L.run(fasta, vcf, o), W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}
  for +hdl: {dfs == L.defs(String.concat(cs)) : B.Defs}
  {M.launch(W.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine_go(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, x, ha, h, hb, est, inv, hbi0, hn0, hdl):
  +fa = B.Fasta.parse(fasta)
  +T = L.run(fasta, vcf, o)
  +bd = M.bound(argv, fasta, vcf, cs)
  +DV = L.defs(vcf)
  +hfb = PB.and_true_r(E.all_bytes(argv), Bool.and(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs))), hb)
  +htx = PB.and_true_r(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs)), hfb)
  +hbfa = FB.fa_bytes_parse(fasta, PB.and_true_l(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs)), hfb))
  +est0 = AB.subst(Maybe<&2, B.Cfg>, m => {WD.wstart_st(dfs, W.start.k(Norm.start.of(m))) == WD.mkWSt(fa, x) : W.St}, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha, est)
  +hbi1 = AB.subst(Maybe<&2, B.Cfg>, m => {BD.biW(W.St{DD.start_st(dfs, Norm.start.of(m)), W.BNone{}}, cs) == True{} : Bool}, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha, hbi0)
  +hn1 = AB.subst(Maybe<&2, B.Cfg>, m => {Nat.is_le(BD.needW(fa, T, W.St{DD.start_st(dfs, Norm.start.of(m)), W.BNone{}}, cs, False{}, Pr.More{}, ""), bd) == True{} : Bool}, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha, hn0)
  +hbi = AB.subst(W.St, z => {BD.biW(z, cs) == True{} : Bool}, st0(DV, o, ref, vcfpath), WD.mkWSt(fa, x), est0, hbi1)
  +hn = AB.subst(W.St, z => {Nat.is_le(BD.needW(fa, T, z, cs, False{}, Pr.More{}, ""), bd) == True{} : Bool}, st0(DV, o, ref, vcfpath), WD.mkWSt(fa, x), est0, hn1)
  inv1 = AB.subst(B.Defs, d => WD.InvW(d, fa, R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, d, o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{}), dfs, L.defs(String.concat(cs)), hdl, inv)
  inv0 = AB.subst(String, z => WD.InvW(L.defs(z), fa, R.finish(L.run.go(B.Text.lines(z), fa, L.defs(z), o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{}), String.concat(cs), vcf, h, inv1)
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {M.launch(W.start.k(Norm.start.of(_)), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, T}} : Maybe<&2, M.Launch>}
  %Equal.sym(Maybe<&2, R.Report>, M.result(M.drive(bd, fa, M.DSt{st0(DV, o, ref, vcfpath), Pr.More{}, cs, False{}, 0n, True{}, "", Nil{}, None{}}), bd), Some{T},
    drive_ok(DV, bd, fa, T, bd, hbfa, M.DSt{st0(DV, o, ref, vcfpath), Pr.More{}, cs, False{}, 0n, True{}, "", Nil{}, None{}},
      (x, (est0, (inv0, ({==}, (htx, (hbi, (hn, hn))))))))) :
    {M.launch.of(_, ref, vcfpath) == Some{M.Launch{ref, vcfpath, T}} : Maybe<&2, M.Launch>}
  {==}


law machine_w:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for so: &x: WD.WPic -> ({WD.wstart_st(dfs, W.start(argv)) == WD.mkWSt(B.Fasta.parse(fasta), x) : W.St}
    & ({WD.wstart_paths(W.start(argv)) == Some{DD.Paths{ref, vcfpath}} : Maybe<&2, DD.Paths>}
    & WD.InvW(dfs, B.Fasta.parse(fasta), R.finish(L.run.go(B.Text.lines(String.concat(cs)), B.Fasta.parse(fasta), dfs, o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{})))
  for bud: {BD.biW(W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs) == True{} : Bool}
    & {Nat.is_le(BD.needW(B.Fasta.parse(fasta), L.run(fasta, vcf, o), W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}
  for +hdl: {dfs == L.defs(String.concat(cs)) : B.Defs}
  {M.launch(W.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine_w(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, h, hb, ha, so, bud, hdl):
  (+x, s1) = so
  (+est, s2) = s1
  (paths, inv) = s2
  (hbi0, hn0) = bud
  machine_go(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, x, ha, h, hb, est, inv, hbi0, hn0, hdl)

# The law machine for the parallel machine, every variable reusable.
law machine_h:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  {M.launch(W.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine_h(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb):
  +D = L.defs(String.concat(cs))
  machine_w(D, argv, o, ref, vcfpath, fasta, vcf, cs, h, hb, ha,
    WS.wstart(D, B.Fasta.parse(fasta), argv, o, ref, vcfpath, cs, ha, PB.and_true_l(E.all_bytes(argv), Bool.and(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs))), hb), {==}),
    API.bud_startW(D, argv, o, ref, vcfpath, fasta, vcf, cs, ha, h, hb), {==})
