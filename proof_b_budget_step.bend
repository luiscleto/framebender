import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./norm_seq.bend as Norm
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SA
import ./proof_b_drive_step.bend as DS
import ./proof_b_drive_pump.bend as DP
import ./proof_b_drivedefs.bend as DD
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_adv.bend as BA
import ./proof_b_bud_fed.bend as BF
import ./proof_b_bud_hop.bend as BH
import ./proof_b_bud_out.bend as BO
import ./proof_b_budget_ho.bend as HO
import ./proof_b_budget_dig.bend as G
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_base.bend as PB

# The budget's per-step lemmas (notes/bytes_proofs_budget.md): one driver step
# lowers need by 1 + its reads. Layers:
#   - a step is feed / feed_eof / set_win, then go (pump over advance);
#   - go_bud: the pump keeps HO + RD(next) + WA within what it started with,
#     by induction over the pump with adv_ok (the simulation) and adv_bud /
#     adv_bi (what each advance does to WA and bi);
#   - the feeds keep WA and bi (the text still to come is the same);
#   - the API's bud_* (proof_b_budget_api.bend) are arithmetic on top.

# ---------------------------------------------------------------------------
# What a step guarantees for the budget
# ---------------------------------------------------------------------------

# adv_bud / adv_bi: walking advance's paths (as the adv area's adv_ok).
def adv_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.AdvB(fa, cs, p, Norm.advance(S.mkSt(fa, p))):
  BA.c2b(fa, cs, p, Norm.advance(S.mkSt(fa, p)), BA.adv_c(fa, T, cs, O, N, p, hb, hw, hr, hg, ha, hbi))

def adv_bi(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.AdvBi(cs, Norm.advance(S.mkSt(fa, p))):
  BA.c2bi(fa, cs, p, Norm.advance(S.mkSt(fa, p)), BA.adv_c(fa, T, cs, O, N, p, hb, hw, hr, hg, ha, hbi))

# The step's end: out keeps the state's WA, bi and next.
def out_was(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +nx: Pr.Next) ->
  {BN.WAS(fa, BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs) == BN.WAS(fa, S.mkSt(fa, p), cs) : Nat}:
  BO.out_was(fa, cs, p, nx)

def out_bi(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +nx: Pr.Next) ->
  {BN.biS(BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs) == BN.biS(S.mkSt(fa, p), cs) : Bool}:
  BO.out_bi(fa, cs, p, nx)

def out_snx(+fa: List<&2, B.Contig>, +p: S.StP, +nx: Pr.Next) -> {BN.snx(Norm.out(S.mkSt(fa, p), nx)) == nx : Pr.Next}:
  BO.out_snx(fa, p, nx)

# A yield hands out at least 256 bytes.
def yield_out(+fa: List<&2, B.Contig>, +p: S.StP, +hw: {S.WF(fa, p) == True{} : Bool}, +hy: {BD.yc(p) == True{} : Bool}, +t: String,
  +ht: {BN.sout(Norm.out(S.mkSt(fa, p), Pr.Ask{Nil{}})) == Some{t} : Maybe<&2, String>}) ->
  {Nat.is_le(256n, String.length(t)) == True{} : Bool}:
  BH.yield_out(fa, p, hw, hy, t, ht)

# The end of the run: Finish, or (String mode, output past 2^30) a hand-out
# of 2^30 bytes and Ask{[]}.
def fin_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP,
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, BN.WAS(fa, S.mkSt(fa, p), cs), Norm.finish(S.mkSt(fa, p))):
  BO.fin_bud(fa, T, cs, O, p, hw, hbi)

# ---------------------------------------------------------------------------
# The pump
# ---------------------------------------------------------------------------

def bud_mono(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +W1: Nat, +W2: Nat, -s: Norm.Step,
  h: BD.BudS(fa, T, cs, O, W1, s), +hw: {Nat.is_le(W1, W2) == True{} : Bool}) -> BD.BudS(fa, T, cs, O, W2, s):
  match h:
    case (hbi, k):
      (hbi, +t => ht => hp => +r => er => +w => ew => N.le_trans(Nat.add(BN.HO(T, String.append(O, t)), Nat.add(r, w)), Nat.add(BN.HO(T, O), W1), Nat.add(BN.HO(T, O), W2),
        k(t, ht, hp, r, er, w, ew), N.le_add_mono_l(BN.HO(T, O), W1, W2, hw)))

def OL(+O: String, +t: String) -> {Nat.is_le(String.length(O), String.length(String.append(O, t))) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(String.length(O), z) == True{} : Bool}, Nat.add(String.length(O), String.length(t)), String.length(String.append(O, t)),
    Equal.sym(Nat, String.length(String.append(O, t)), Nat.add(String.length(O), String.length(t)), G.slen_app(O, t)), N.le_add_r(String.length(O), String.length(t)))

# HO never grows.
def hoa(+T: R.Report, +O: String, +t: String) -> {Nat.is_le(BN.HO(T, String.append(O, t)), BN.HO(T, O)) == True{} : Bool}:
  HO.ho_anti(String.length(R.Report.out(T)), String.length(O), String.length(String.append(O, t)), 256n, {==}, OL(O, t))

# A step ending in out(st, nx) with RD(nx) + WA(st) <= W0 (WA(st) from out_was).
def out_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p2: S.StP, +nx: Pr.Next, +W0: Nat,
  +hbi: {BN.biS(S.mkSt(fa, p2), cs) == True{} : Bool},
  +hw: {Nat.is_le(Nat.add(BN.RD(nx), BN.WAS(fa, S.mkSt(fa, p2), cs)), W0) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, W0, Norm.out(S.mkSt(fa, p2), nx)):
  (Equal.trans(Bool, BN.biS(BN.sst(Norm.out(S.mkSt(fa, p2), nx)), cs), BN.biS(S.mkSt(fa, p2), cs), True{}, out_bi(fa, cs, p2, nx), hbi),
    +t => ht => hp => +r => er => +w => ew =>
      +er2 = Equal.trans(Nat, r, BN.RD(BN.snx(Norm.out(S.mkSt(fa, p2), nx))), BN.RD(nx), Equal.sym(Nat, BN.RD(BN.snx(Norm.out(S.mkSt(fa, p2), nx))), r, er),
        Equal.cong(Pr.Next, Nat, z => BN.RD(z), BN.snx(Norm.out(S.mkSt(fa, p2), nx)), nx, out_snx(fa, p2, nx)))
      +ew2 = Equal.trans(Nat, w, BN.WAS(fa, BN.sst(Norm.out(S.mkSt(fa, p2), nx)), cs), BN.WAS(fa, S.mkSt(fa, p2), cs), Equal.sym(Nat, BN.WAS(fa, BN.sst(Norm.out(S.mkSt(fa, p2), nx)), cs), w, ew),
        out_was(fa, cs, p2, nx))
      +hrw = AB.subst(Nat, z => {Nat.is_le(Nat.add(z, w), W0) == True{} : Bool}, BN.RD(nx), r, Equal.sym(Nat, r, BN.RD(nx), er2),
        AB.subst(Nat, z => {Nat.is_le(Nat.add(BN.RD(nx), z), W0) == True{} : Bool}, BN.WAS(fa, S.mkSt(fa, p2), cs), w, Equal.sym(Nat, w, BN.WAS(fa, S.mkSt(fa, p2), cs), ew2), hw))
      PB.le_add(BN.HO(T, String.append(O, t)), BN.HO(T, O), Nat.add(r, w), W0, hoa(T, O, t), hrw))

# Idle: More before the end of the file, else the end of the run.
def idle_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p2: S.StP, +W0: Nat,
  +hw2: {S.WF(fa, p2) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p2), cs) == True{} : Bool},
  +hW: {Nat.is_le(BN.WAS(fa, S.mkSt(fa, p2), cs), W0) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, W0, Norm.idle(S.mkSt(fa, p2))):
  match p2:
    case S.StP{+o, +md, +src, +pd, False{}, +back, +wp, +asked, +fneed, +dfs}:
      out_bud(fa, T, cs, O, S.StP{o, md, src, pd, False{}, back, wp, asked, fneed, dfs}, Pr.More{}, W0, hbi, hW)
    case S.StP{+o, +md, +src, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      bud_mono(fa, T, cs, O, BN.WAS(fa, S.mkSt(fa, S.StP{o, md, src, pd, True{}, back, wp, asked, fneed, dfs}), cs), W0, Norm.finish(S.mkSt(fa, S.StP{o, md, src, pd, True{}, back, wp, asked, fneed, dfs})),
        fin_bud(fa, T, cs, O, S.StP{o, md, src, pd, True{}, back, wp, asked, fneed, dfs}, hw2, hbi), hW)

# A yield: the state as it was, its test passed, out with Ask{[]}: HO pays.
def yb.k(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP,
  +hw: {S.WF(fa, p) == True{} : Bool}, +hy: {BD.yc(p) == True{} : Bool}, +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, BD.WP(fa, cs, p), Norm.out(S.mkSt(fa, p), Pr.Ask{Nil{}})):
  +nx = {Pr.Ask{Nil{}} : Pr.Next}
  (Equal.trans(Bool, BN.biS(BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs), BN.biS(S.mkSt(fa, p), cs), True{}, out_bi(fa, cs, p, nx), hbi),
    +t => +ht => +hp => +r => er => +w => ew =>
      +X = String.length(R.Report.out(T))
      +W = BD.WP(fa, cs, p)
      +er2 = Equal.trans(Nat, r, BN.RD(BN.snx(Norm.out(S.mkSt(fa, p), nx))), 1n, Equal.sym(Nat, BN.RD(BN.snx(Norm.out(S.mkSt(fa, p), nx))), r, er),
        Equal.cong(Pr.Next, Nat, z => BN.RD(z), BN.snx(Norm.out(S.mkSt(fa, p), nx)), nx, out_snx(fa, p, nx)))
      +ew2 = Equal.trans(Nat, w, BN.WAS(fa, BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs), W, Equal.sym(Nat, BN.WAS(fa, BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs), w, ew),
        out_was(fa, cs, p, nx))
      +el = G.slen_app(O, t)
      +hp2 = AB.subst(Nat, z => {Nat.is_le(z, X) == True{} : Bool}, String.length(String.append(O, t)), Nat.add(String.length(O), String.length(t)), el, hp)
      +hd = HO.ho_drop(X, String.length(O), String.length(t), 256n, {==}, yield_out(fa, p, hw, hy, t, ht), hp2)
      +hd2 = AB.subst(Nat, z => {Nat.is_le(1n+Nat.div(Nat.sub(X, z), 256n), BN.HO(T, O)) == True{} : Bool}, Nat.add(String.length(O), String.length(t)), String.length(String.append(O, t)),
        Equal.sym(Nat, String.length(String.append(O, t)), Nat.add(String.length(O), String.length(t)), el), hd)
      +H2 = BN.HO(T, String.append(O, t))
      +h3 = N.le_add_mono_r(W, 1n+H2, BN.HO(T, O), hd2)
      +h4 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(BN.HO(T, O), W)) == True{} : Bool}, 1n+Nat.add(H2, W), Nat.add(H2, 1n+W), Equal.sym(Nat, Nat.add(H2, 1n+W), 1n+Nat.add(H2, W), N.add_succ(H2, W)), h3)
      AB.subst(Nat, z => {Nat.is_le(Nat.add(H2, Nat.add(z, w)), Nat.add(BN.HO(T, O), W)) == True{} : Bool}, 1n, r, Equal.sym(Nat, r, 1n, er2),
        AB.subst(Nat, z => {Nat.is_le(Nat.add(H2, Nat.add(1n, z)), Nat.add(BN.HO(T, O), W)) == True{} : Bool}, W, w, Equal.sym(Nat, w, W, ew2), h4)))

def yield_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP, -st: Norm.St,
  +hw: {S.WF(fa, p) == True{} : Bool},
  ab: {st == S.mkSt(fa, p) : Norm.St} & {BD.yc(p) == True{} : Bool}, abi: {BN.biS(st, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, BD.WP(fa, cs, p), Norm.out(st, Pr.Ask{Nil{}})):
  match ab:
    case (+est, +hy):
      +bi2 = AB.subst(Norm.St, z => {BN.biS(z, cs) == True{} : Bool}, st, S.mkSt(fa, p), est, abi)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p), est) : BD.BudS(fa, T, cs, O, BD.WP(fa, cs, p), Norm.out(_, Pr.Ask{Nil{}}))
      yb.k(fa, T, cs, O, p, hw, hy, bi2)

def IHG(+g: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>) -> Type:
  @q: S.StP -> {S.WF(fa, q) == True{} : Bool} -> {Nat.is_le(S.measure(q), g) == True{} : Bool} ->
    S.AdvG(fa, T, cs, O, N, q, Norm.advance(S.mkSt(fa, q))) -> BD.AdvB(fa, cs, q, Norm.advance(S.mkSt(fa, q))) -> BD.AdvBi(cs, Norm.advance(S.mkSt(fa, q))) ->
    BD.BudS(fa, T, cs, O, BD.WP(fa, cs, q), Norm.pump(1n+g, Norm.advance(S.mkSt(fa, q))))

# A line handled (Went): on with the next state's picture p2.
def went_k(+g: Nat, -st: Norm.St, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +p2: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hf: {Nat.is_le(S.measure(p), 1n+g) == True{} : Bool},
  +est: {st == S.mkSt(fa, p2) : Norm.St},
  +wf2: {S.WF(fa, p2) == True{} : Bool},
  +er2: {S.report(fa, cs, O, N, p2) == T : R.Report},
  +elt: {Nat.is_lt(S.measure(p2), S.measure(p)) == True{} : Bool},
  +eask2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +eg2: {S.guard(O, N, p2) == True{} : Bool},
  ab: {Nat.is_le(BN.WAS(fa, st, cs), BD.WP(fa, cs, p)) == True{} : Bool},
  abi: {BN.biS(st, cs) == True{} : Bool},
  ih: IHG(g, fa, T, cs, O, N)) ->
  BD.BudS(fa, T, cs, O, BD.WP(fa, cs, p), Norm.pump(1n+(1n+g), Norm.Went{st})):
  ?TODO


# The pump: from p (advance's result a), the step keeps the budget.
def pb_go(+f: Nat, a: Norm.Adv, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool},
  ag: S.AdvG(fa, T, cs, O, N, p, a), ab: BD.AdvB(fa, cs, p, a), abi: BD.AdvBi(cs, a)) ->
  BD.BudS(fa, T, cs, O, BD.WP(fa, cs, p), Norm.pump(1n+f, a)):
  ?TODO



# go from a good state with nothing asked: the pump with its fuel.
def go_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +q: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, q) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, q) == T : R.Report},
  +ha: {S.StP.asked(q) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hg: {S.guard(O, N, q) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, q), cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, BD.WP(fa, cs, q), Norm.go(S.mkSt(fa, q))):
  match q:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +Q = {S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(src)), (P.mkSrcs(src), DP.fuelN(src)), DP.fuel_eq(src)) :
        BD.BudS(fa, T, cs, O, BD.WP(fa, cs, Q), Norm.go.k(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs))
      pb_go(Nat.add(DP.fuelN(src), 1n), Norm.advance(S.mkSt(fa, Q)), fa, T, cs, O, N, Q, hb, hw, DS.meas_le(dfs, md, o, src, pd, eof, back, wp, asked, fneed),
        SA.adv_ok(fa, T, cs, O, N, Q, hb, hw, hr, hg), adv_bud(fa, T, cs, O, N, Q, hb, hw, hr, hg, ha, hbi), adv_bi(fa, T, cs, O, N, Q, hb, hw, hr, hg, ha, hbi))

# ---------------------------------------------------------------------------
# The inputs (sub-lemmas): the state after feed / feed_eof / set_win is good,
# stands for the same report, has nothing asked, and keeps WA and bi.
# ---------------------------------------------------------------------------

def chunk_fed(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DD.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), c <> cs) == True{} : Bool},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, p), Norm.feed(S.mkSt(fa, p), E.enc(c))):
  BF.chunk_fed(fa, T, c, cs, O, N, p, hb, hm, hr, hg, hbi, hcb, hcn)

def eof_fed(+fa: List<&2, B.Contig>, +T: R.Report, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DD.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), Nil{}) == True{} : Bool}) ->
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, p), Norm.feed_eof(S.mkSt(fa, p))):
  BF.eof_fed(fa, T, O, N, p, hb, hm, hr, hg, hbi)

def ref_fed(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +rs: List<&2, Pr.Req>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  +hq: {E.reqs_ok(rs) == True{} : Bool},
  +hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, p), Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs))):
  BF.ref_fed(fa, T, cs, rs, O, N, p, hb, hw, hr, ha, hq, hp, hmr, hg, hbi)

# What a state stands for begins with what was written (with the guard).
def hop(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool}) ->
  {Nat.is_le(String.length(O), String.length(R.Report.out(T))) == True{} : Bool}:
  BH.hop(fa, T, cs, O, N, p, hr, hg)

def fed.k(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +W: Nat, -st: Norm.St, +q: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool}, +eq: {st == S.mkSt(fa, q) : Norm.St}, +wq: {S.WF(fa, q) == True{} : Bool}, +rq: {S.report(fa, cs, O, N, q) == T : R.Report},
  +gq: {S.guard(O, N, q) == True{} : Bool}, +aq: {S.StP.asked(q) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hWq: {Nat.is_le(BD.WP(fa, cs, q), W) == True{} : Bool}, +biq: {BN.biS(S.mkSt(fa, q), cs) == True{} : Bool}) -> BD.BudS(fa, T, cs, O, W, Norm.go(st)):
  %Equal.sym(Norm.St, st, S.mkSt(fa, q), eq) : BD.BudS(fa, T, cs, O, W, Norm.go(_))
  bud_mono(fa, T, cs, O, BD.WP(fa, cs, q), W, Norm.go(S.mkSt(fa, q)), go_bud(fa, T, cs, O, N, q, hb, wq, rq, aq, gq, biq), hWq)

# go after an input: from the input's FedG.
def fed_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +W: Nat, -st: Norm.St,
  +hb: {PC.fa_bytes(fa) == True{} : Bool}, h: BD.FedG(fa, T, cs, O, N, W, st)) -> BD.BudS(fa, T, cs, O, W, Norm.go(st)):
  (+q, h1) = h
  (eq, h2) = h1
  (wq, h3) = h2
  (rq, h4) = h3
  (gq, h5) = h4
  (aq, h6) = h5
  (hWq, biq) = h6
  fed.k(fa, T, cs, O, N, W, st, q, hb, eq, wq, rq, gq, aq, hWq, biq)


# ---------------------------------------------------------------------------
# The API's per-step lemmas (proof_b_budget_api.bend calls these)
# ---------------------------------------------------------------------------

# need's arithmetic: L <= M.
def ar_chunk(+a: Nat, +L: Nat, +M: Nat, +h: {Nat.is_le(L, M) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.add(Nat.add(a, 1n), Nat.add(2n, L)), Nat.add(0n, 1n)), Nat.add(Nat.add(1n+a, 1n), Nat.add(2n, M))) == True{} : Bool}:
  +X = Nat.add(Nat.add(a, 1n), Nat.add(2n, L))
  AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.add(1n+a, 1n), Nat.add(2n, M))) == True{} : Bool}, 1n+X, Nat.add(X, 1n), Equal.sym(Nat, Nat.add(X, 1n), 1n+X, N.add_one(X)),
    N.le_add_mono_l(Nat.add(a, 1n), Nat.add(2n, L), Nat.add(2n, M), N.le_add_mono_l(2n, L, M, h)))

def ar_eof(+L: Nat, +M: Nat, +h: {Nat.is_le(L, M) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.add(Nat.add(0n, 0n), Nat.add(2n, L)), Nat.add(0n, 1n)), Nat.add(Nat.add(0n, 1n), Nat.add(2n, M))) == True{} : Bool}:
  +X = Nat.add(2n, L)
  AB.subst(Nat, z => {Nat.is_le(z, 1n+Nat.add(2n, M)) == True{} : Bool}, 1n+X, Nat.add(X, 1n), Equal.sym(Nat, Nat.add(X, 1n), 1n+X, N.add_one(X)),
    N.le_add_mono_l(2n, L, M, h))

def ar_ref(+Bs: Nat, +L: Nat, +H: Nat, +W: Nat, +R0: Nat, +h: {Nat.is_le(L, Nat.add(H, W)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.add(Bs, Nat.add(2n, L)), Nat.add(R0, 1n)), Nat.add(Bs, Nat.add(2n, Nat.add(H, 1n+Nat.add(R0, W))))) == True{} : Bool}:
  +K = Nat.add(R0, 1n)
  +M = Nat.add(H, W)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Bs, Nat.add(2n, L)), K), Nat.add(Bs, Nat.add(Nat.add(2n, L), K)), Nat.add(Bs, Nat.add(2n, Nat.add(L, K))),
    N.add_assoc(Bs, Nat.add(2n, L), K), Equal.cong(Nat, Nat, z => Nat.add(Bs, z), Nat.add(Nat.add(2n, L), K), Nat.add(2n, Nat.add(L, K)), N.add_assoc(2n, L, K)))
  +e2 = Equal.trans(Nat, Nat.add(H, 1n+Nat.add(R0, W)), Nat.add(H, Nat.add(K, W)), Nat.add(K, M),
    Equal.cong(Nat, Nat, z => Nat.add(H, Nat.add(z, W)), 1n+R0, K, Equal.sym(Nat, K, 1n+R0, N.add_one(R0))),
    N.add_left_comm(H, K, W))
  +h1 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(K, M)) == True{} : Bool}, Nat.add(K, L), Nat.add(L, K), N.add_comm(K, L), N.le_add_mono_l(K, L, M, h))
  +h2 = N.le_add_mono_l(Bs, Nat.add(2n, Nat.add(L, K)), Nat.add(2n, Nat.add(K, M)), N.le_add_mono_l(2n, Nat.add(L, K), Nat.add(K, M), h1))
  AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(Bs, Nat.add(2n, L)), K), Nat.add(Bs, Nat.add(2n, z))) == True{} : Bool}, Nat.add(K, M), Nat.add(H, 1n+Nat.add(R0, W)),
    Equal.sym(Nat, Nat.add(H, 1n+Nat.add(R0, W)), Nat.add(K, M), e2),
    AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Bs, Nat.add(2n, Nat.add(K, M)))) == True{} : Bool}, Nat.add(Bs, Nat.add(2n, Nat.add(L, K))), Nat.add(Nat.add(Bs, Nat.add(2n, L)), K),
      Equal.sym(Nat, Nat.add(Nat.add(Bs, Nat.add(2n, L)), K), Nat.add(Bs, Nat.add(2n, Nat.add(L, K))), e1), h2))

# From a step's BudS and its next picture: bi there, and the inequality.
def L2(+fa: List<&2, B.Contig>, +T: R.Report, +cs2: List<&2, String>, +O: String, +t: String, +p2: S.StP, +nx2: Pr.Next) -> Nat:
  Nat.add(BN.HO(T, String.append(O, t)), Nat.add(BN.RD(nx2), BN.WAS(fa, S.mkSt(fa, p2), cs2)))

def bud_bi(+fa: List<&2, B.Contig>, +T: R.Report, +cs2: List<&2, String>, +O: String, +W0: Nat, -s: Norm.Step, h: BD.BudS(fa, T, cs2, O, W0, s), +p2: S.StP,
  +hst: {BN.sst(s) == S.mkSt(fa, p2) : Norm.St}) -> {BN.biS(S.mkSt(fa, p2), cs2) == True{} : Bool}:
  match h:
    case (bi2, k):
      AB.subst(Norm.St, z => {BN.biS(z, cs2) == True{} : Bool}, BN.sst(s), S.mkSt(fa, p2), hst, bi2)

def bud_le(+fa: List<&2, B.Contig>, +T: R.Report, +cs2: List<&2, String>, +O: String, +W0: Nat, -s: Norm.Step, h: BD.BudS(fa, T, cs2, O, W0, s), +p2: S.StP, +nx2: Pr.Next, +t: String,
  +hst: {BN.sst(s) == S.mkSt(fa, p2) : Norm.St}, +hnx: {BN.snx(s) == nx2 : Pr.Next}, +hout: {BN.sout(s) == Some{t} : Maybe<&2, String>},
  +hpre: {Nat.is_le(String.length(String.append(O, t)), String.length(R.Report.out(T))) == True{} : Bool}) ->
  {Nat.is_le(L2(fa, T, cs2, O, t, p2, nx2), Nat.add(BN.HO(T, O), W0)) == True{} : Bool}:
  match h:
    case (bi2, k):
      k(t, hout, hpre, BN.RD(nx2), Equal.cong(Pr.Next, Nat, z => BN.RD(z), BN.snx(s), nx2, hnx),
        BN.WAS(fa, S.mkSt(fa, p2), cs2), Equal.cong(Norm.St, Nat, z => BN.WAS(fa, z, cs2), BN.sst(s), S.mkSt(fa, p2), hst))

def SC(+fa: List<&2, B.Contig>, +p: S.StP, +c: String) -> Norm.Step:
  Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})

def bud_chunk_h(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +c: String,
  +cs: List<&2, String>,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +p2: S.StP, +nx2: Pr.Next, +t: String,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DD.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.bi(fa, T, p, c <> cs, False{}, Pr.More{}, O) == True{} : Bool},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool},
  +hst: {BN.sst(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})) == S.mkSt(fa, p2) : Norm.St},
  +hnx: {BN.snx(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})) == nx2 : Pr.Next},
  +hout: {BN.sout(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})) == Some{t} : Maybe<&2, String>},
  +hw2: {S.WF(fa, p2) == True{} : Bool},
  +hr2: {S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}))), p2) == T : R.Report},
  +hg2: {S.guard(String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}))), p2) == True{} : Bool}) ->
  {BN.bi(fa, T, p2, cs, False{}, nx2, String.append(O, t)) == True{} : Bool}
  & {Nat.is_le(Nat.add(BN.need(fa, T, p2, cs, False{}, nx2, String.append(O, t)), Nat.add(0n, 1n)), BN.need(fa, T, p, c <> cs, False{}, Pr.More{}, O)) == True{} : Bool}:
  +W0 = BD.WP(fa, c <> cs, p)
  +hpre = hop(fa, T, cs, String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}))), p2, hr2, hg2)
  (bud_bi(fa, T, cs, O, W0, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}),
      fed_bud(fa, T, cs, O, N, W0, Norm.feed(S.mkSt(fa, p), E.enc(c)), hb, chunk_fed(fa, T, c, cs, O, N, p, hb, hm, hr, hg, hbi, hcb, hcn)), p2, hst),
    ar_chunk(List.length(&2, String, cs), L2(fa, T, cs, O, t, p2, nx2), Nat.add(BN.HO(T, O), W0),
      bud_le(fa, T, cs, O, W0, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}),
        fed_bud(fa, T, cs, O, N, W0, Norm.feed(S.mkSt(fa, p), E.enc(c)), hb, chunk_fed(fa, T, c, cs, O, N, p, hb, hm, hr, hg, hbi, hcb, hcn)), p2, nx2, t, hst, hnx, hout, hpre)))

def bud_eof_h(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +p2: S.StP, +nx2: Pr.Next, +t: String,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DD.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.bi(fa, T, p, Nil{}, False{}, Pr.More{}, O) == True{} : Bool},
  +hst: {BN.sst(Norm.step(S.mkSt(fa, p), Pr.Eof{})) == S.mkSt(fa, p2) : Norm.St},
  +hnx: {BN.snx(Norm.step(S.mkSt(fa, p), Pr.Eof{})) == nx2 : Pr.Next},
  +hout: {BN.sout(Norm.step(S.mkSt(fa, p), Pr.Eof{})) == Some{t} : Maybe<&2, String>},
  +hw2: {S.WF(fa, p2) == True{} : Bool},
  +hr2: {S.report(fa, Nil{}, String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Eof{}))), p2) == T : R.Report},
  +hg2: {S.guard(String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Eof{}))), p2) == True{} : Bool}) ->
  {BN.bi(fa, T, p2, Nil{}, True{}, nx2, String.append(O, t)) == True{} : Bool}
  & {Nat.is_le(Nat.add(BN.need(fa, T, p2, Nil{}, True{}, nx2, String.append(O, t)), Nat.add(0n, 1n)), BN.need(fa, T, p, Nil{}, False{}, Pr.More{}, O)) == True{} : Bool}:
  +W0 = BD.WP(fa, Nil{}, p)
  +hpre = hop(fa, T, Nil{}, String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Eof{}))), p2, hr2, hg2)
  (bud_bi(fa, T, Nil{}, O, W0, Norm.step(S.mkSt(fa, p), Pr.Eof{}),
      fed_bud(fa, T, Nil{}, O, N, W0, Norm.feed_eof(S.mkSt(fa, p)), hb, eof_fed(fa, T, O, N, p, hb, hm, hr, hg, hbi)), p2, hst),
    ar_eof(L2(fa, T, Nil{}, O, t, p2, nx2), Nat.add(BN.HO(T, O), W0),
      bud_le(fa, T, Nil{}, O, W0, Norm.step(S.mkSt(fa, p), Pr.Eof{}),
        fed_bud(fa, T, Nil{}, O, N, W0, Norm.feed_eof(S.mkSt(fa, p)), hb, eof_fed(fa, T, O, N, p, hb, hm, hr, hg, hbi)), p2, nx2, t, hst, hnx, hout, hpre)))

def bud_ref_h(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +cs: List<&2, String>,
  +de: Bool,
  +rs: List<&2, Pr.Req>,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +p2: S.StP, +nx2: Pr.Next, +t: String,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  +hq: {E.reqs_ok(rs) == True{} : Bool},
  +hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.bi(fa, T, p, cs, de, Pr.Ask{rs}, O) == True{} : Bool},
  +hst: {BN.sst(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})) == S.mkSt(fa, p2) : Norm.St},
  +hnx: {BN.snx(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})) == nx2 : Pr.Next},
  +hout: {BN.sout(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})) == Some{t} : Maybe<&2, String>},
  +hw2: {S.WF(fa, p2) == True{} : Bool},
  +hr2: {S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))), p2) == T : R.Report},
  +hg2: {S.guard(String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))), p2) == True{} : Bool}) ->
  {BN.bi(fa, T, p2, cs, de, nx2, String.append(O, t)) == True{} : Bool}
  & {Nat.is_le(Nat.add(BN.need(fa, T, p2, cs, de, nx2, String.append(O, t)), Nat.add(List.length(&2, Pr.Req, rs), 1n)), BN.need(fa, T, p, cs, de, Pr.Ask{rs}, O)) == True{} : Bool}:
  +W0 = BD.WP(fa, cs, p)
  +hpre = hop(fa, T, cs, String.append(O, t), List.append(&2, B.Note, N, BN.sns(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))), p2, hr2, hg2)
  (bud_bi(fa, T, cs, O, W0, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}),
      fed_bud(fa, T, cs, O, N, W0, Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), hb, ref_fed(fa, T, cs, rs, O, N, p, hb, hw, hr, ha, hq, hp, hmr, hg, hbi)), p2, hst),
    ar_ref(Nat.add(List.length(&2, String, cs), BN.pick(Bool.not(de), 1n)), L2(fa, T, cs, O, t, p2, nx2), BN.HO(T, O), W0, List.length(&2, Pr.Req, rs),
      bud_le(fa, T, cs, O, W0, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}),
        fed_bud(fa, T, cs, O, N, W0, Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), hb, ref_fed(fa, T, cs, rs, O, N, p, hb, hw, hr, ha, hq, hp, hmr, hg, hbi)), p2, nx2, t, hst, hnx, hout, hpre)))
