import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BDs
import ./proof_b_budget_step.bend as BS
import ./proof_base.bend as PB
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-halves@0.1.0.0/halves.bend as HH
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as QB
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_api.bend as API
import ./proof_e_bud_step.bend as ST
import ./proof_e_bud_list.bend as LI
import ./proof_e_bud_ph1.bend as H1
import ./proof_e_bud_comb.bend as CB
import ./proof_e_mach_dup.bend as DU

# Phase E, area E2: the step that closes a batch (W.plan): the plan's Ask
# (its reads, at most two per piece), or with no reads the tasks and the
# combine of the first piece in the same step.

# A step of Q handed out with the planned batch.
law wrap_ask:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +ef: Bool
  for +O: String
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +W0: Nat
  for s: Norm.Step
  for +hpl: {BD.plts(PT.mkPls(ps)) == PT.texts(ps) : List<&2, String>}
  for h: BDs.BudS(fa, T, List.append(&2, String, PT.texts(ps), cs), O, W0, s)
  ST.BudW(fa, T, cs, ef, O, Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), BD.XK(cs)), W.wrap(s, W.BAsk{PT.mkPls(ps), e}))

def wrap_ask(fa, T, cs, ef, O, ps, e, W0, s, hpl, h):
  match s:
    case Norm.Step{st, b, +ns, +nx}:
      (hbi, k) = h
      +L = List.append(&2, String, PT.texts(ps), cs)
      hnf => (%Equal.sym(List<&2, String>, BD.plts(PT.mkPls(ps)), PT.texts(ps), hpl) : {BN.biS(st, List.append(&2, String, _, cs)) == True{} : Bool}; hbi,
        +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), BD.XK(cs))) == True{} : Bool};
          %Equal.sym(List<&2, String>, BD.plts(PT.mkPls(ps)), PT.texts(ps), hpl) :
            {Nat.is_le(Nat.add(BN.needS(fa, T, st, List.append(&2, String, _, cs), False{}, nx, String.append(O, t)), BD.XK(cs)), Nat.add(ST.VQ(T, L, False{}, O, W0), BD.XK(cs))) == True{} : Bool};
          ST.needs_le(fa, T, L, False{}, O, W0, st, nx, String.append(O, t), BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, L)))

law nil_of_empty:
  for +rs: List<&2, Pr.Req>
  for +h: {List.is_empty(&2, Pr.Req, rs) == True{} : Bool}
  {rs == Nil{} : List<&2, Pr.Req>}

def nil_of_empty(rs, h):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      Empty.absurd({r <> t == Nil{} : List<&2, Pr.Req>}, PB.false_ne_true(h))

# The batch's bound: Q's need over the pieces, its pending reads at most two
# per piece, and the step.
def VP(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP, +ps: List<&2, PT.Pc>) -> Nat:
  Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, Nat.add(1n+Nat.add(List.length(&2, PT.Pc, ps), List.length(&2, PT.Pc, ps)), BDs.WP(fa, List.append(&2, String, PT.texts(ps), cs), p))), BD.XK(cs))

law le_step:
  for +V: Nat
  for +Vp: Nat
  for +n1: Nat
  for +h: {Nat.is_le(V, Vp) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(Vp, Nat.add(0n, 1n)), n1) == True{} : Bool}
  {Nat.is_le(Nat.add(V, Nat.add(0n, 1n)), n1) == True{} : Bool}

def le_step(V, Vp, n1, h, hn):
  N.le_trans(Nat.add(V, 1n), Nat.add(Vp, 1n), n1, N.le_add_mono_r(1n, V, Vp, h), hn)

# The tasks run with the answers (R reads), and the combine starts.
def VC(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP, +ps: List<&2, PT.Pc>) -> Nat:
  Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, BDs.WP(fa, List.append(&2, String, PT.texts(ps), cs), p)), BD.XK(cs))

law run_tasks.k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +R: Nat
  for +n1: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, PT.texts(ps), cs)) == True{} : Bool}
  for +hv: {Nat.is_le(Nat.add(VC(fa, T, cs, O, p, ps), Nat.add(R, 1n)), n1) == True{} : Bool}
  for r: &xs: List<&2, PT.TOutP> -> ({HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))) == PT.mkTOuts(fa, ps, xs) : List<&1, W.TOut>}
    & PT.BatchOK(fa, S.StP.o(p), ps, xs, cs))
  API.KontW(fa, T, W.comb.next(HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))), S.mkSt(fa, p), e), cs, ef, R, n1, O, N)

def run_tasks.k(fa, T, cs, O, N, ef, p, ps, e, R, n1, hb, hm, hst, hg, hr, hby, hps, he, hbi, hv, r):
  (+xs, r1) = r
  (+eqb, hbo) = r1
  %Equal.sym(List<&1, W.TOut>, HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))), PT.mkTOuts(fa, ps, xs), eqb) :
    API.KontW(fa, T, W.comb.next(_, S.mkSt(fa, p), e), cs, ef, R, n1, O, N)
  ST.kont_of(fa, T, W.comb.next(PT.mkTOuts(fa, ps, xs), S.mkSt(fa, p), e), cs, ef, R, n1, VC(fa, T, cs, O, p, ps), O, N,
    CB.comb_bud(fa, T, cs, O, N, ef, p, ps, xs, e, hb, hm, hst, hg, hr, hby, hps, hbo, he, hbi), hv)

law run_tasks:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +R: Nat
  for +n1: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for d: PT.PcsOK(ps, cs) & PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, PT.texts(ps), cs)) == True{} : Bool}
  for +hv: {Nat.is_le(Nat.add(VC(fa, T, cs, O, p, ps), Nat.add(R, 1n)), n1) == True{} : Bool}
  API.KontW(fa, T, W.comb.next(HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))), S.mkSt(fa, p), e), cs, ef, R, n1, O, N)

def run_tasks(fa, T, cs, O, N, ef, p, ps, e, R, n1, hb, hm, hst, hg, hr, hby, d, he, hbi, hv):
  (h1, h2) = d
  run_tasks.k(fa, T, cs, O, N, ef, p, ps, e, R, n1, hb, hm, hst, hg, hr, hby, h1, he, hbi, hv,
    PT.batch(fa, S.StP.o(p), ps, cs, hb, H1.wf_args(fa, p, QB.mo_w(S.WF(fa, p), S.src_empty(S.StP.src(p)), Bool.not(S.StP.eof(p)), Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p)), hm)), hby, h2))

law plan_tasks:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +n1: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for d: PT.PcsOK(ps, cs) & PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, PT.texts(ps), cs)) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(VP(fa, T, cs, O, p, ps), Nat.add(0n, 1n)), n1) == True{} : Bool}
  API.KontW(fa, T, W.comb.next(HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))), S.mkSt(fa, p), e), cs, ef, 0n, n1, O, N)

def plan_tasks(fa, T, cs, O, N, ef, p, ps, e, n1, hb, hm, hst, hg, hr, hby, d, he, hbi, hn):
  +L = List.append(&2, String, PT.texts(ps), cs)
  +Wp = BDs.WP(fa, L, p)
  +m = List.length(&2, PT.Pc, ps)
  run_tasks(fa, T, cs, O, N, ef, p, ps, e, 0n, n1, hb, hm, hst, hg, hr, hby, d, he, hbi,
    le_step(VC(fa, T, cs, O, p, ps), VP(fa, T, cs, O, p, ps), n1,
      N.le_add_mono_r(BD.XK(cs), ST.VQ(T, L, False{}, O, Wp), ST.VQ(T, L, False{}, O, Nat.add(1n+Nat.add(m, m), Wp)),
        H1.vq_mono(T, L, False{}, O, Wp, Nat.add(1n+Nat.add(m, m), Wp), N.le_add_l(Wp, 1n+Nat.add(m, m)))),
      hn))

law plan_if:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +n1: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, PT.texts(ps), cs)) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(VP(fa, T, cs, O, p, ps), Nat.add(0n, 1n)), n1) == True{} : Bool}
  for +b: Bool
  for +hq: {List.is_empty(&2, Pr.Req, PT.reqs_of(ps)) == b : Bool}
  for d: PT.PcsOK(ps, cs) & PT.PcsOK(ps, cs)
  API.KontW(fa, T, W.plan.go(b, S.mkSt(fa, p), PT.mkPls(ps), PT.reqs_of(ps), e), cs, ef, 0n, n1, O, N)

def plan_if(fa, T, cs, O, N, ef, p, ps, e, n1, hb, hm, hst, hg, hr, hby, he, hbi, hn, b, hq, d):
  match b:
    case True{}:
      +e0 = Equal.cong(List<&2, Pr.Req>, List<&1, Pr.Ans>, z => M.truths(fa, z), PT.reqs_of(ps), Nil{}, nil_of_empty(PT.reqs_of(ps), hq))
      %QB.opts_mk(fa, p) : API.KontW(fa, T, W.ask.run(_, PT.mkPls(ps), Nil{}, e), cs, ef, 0n, n1, O, N)
      %e0 : API.KontW(fa, T, W.comb.next(HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(_))), S.mkSt(fa, p), e), cs, ef, 0n, n1, O, N)
      plan_tasks(fa, T, cs, O, N, ef, p, ps, e, n1, hb, hm, hst, hg, hr, hby, d, he, hbi, hn)
    case False{}:
      (h1, h2) = d
      +L = List.append(&2, String, PT.texts(ps), cs)
      +m = List.length(&2, PT.Pc, ps)
      +rq = PT.reqs_of(ps)
      +W0 = Nat.add(1n+List.length(&2, Pr.Req, rq), BDs.WP(fa, L, p))
      +Va = Nat.add(ST.VQ(T, L, False{}, O, W0), BD.XK(cs))
      +hpl = LI.plts_mk(ps, PB.and_true_l(E.all_bytes(PT.texts(ps)), E.pieces_ok(PT.texts(ps)), hby), PB.and_true_r(E.all_bytes(PT.texts(ps)), E.pieces_ok(PT.texts(ps)), hby))
      ST.kont_of(fa, T, W.wrap(Norm.out(S.mkSt(fa, p), Pr.Ask{rq}), W.BAsk{PT.mkPls(ps), e}), cs, ef, 0n, n1, Va, O, N,
        wrap_ask(fa, T, cs, ef, O, ps, e, W0, Norm.out(S.mkSt(fa, p), Pr.Ask{rq}), hpl, BS.out_bud(fa, T, L, O, p, Pr.Ask{rq}, W0, hbi, N.le_refl(W0))),
        le_step(Va, VP(fa, T, cs, O, p, ps), n1,
          N.le_add_mono_r(BD.XK(cs), ST.VQ(T, L, False{}, O, W0), ST.VQ(T, L, False{}, O, Nat.add(1n+Nat.add(m, m), BDs.WP(fa, L, p))),
            H1.vq_mono(T, L, False{}, O, W0, Nat.add(1n+Nat.add(m, m), BDs.WP(fa, L, p)),
              N.le_add_mono_r(BDs.WP(fa, L, p), 1n+List.length(&2, Pr.Req, rq), 1n+Nat.add(m, m), H1.reqs_le(ps, cs, h1)))),
          hn))

def VH(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP, +Hs: List<&2, String>) -> Nat:
  Nat.add(ST.VQ(T, List.append(&2, String, Hs, cs), False{}, O, Nat.add(1n+Nat.add(List.length(&2, String, Hs), List.length(&2, String, Hs)), BDs.WP(fa, List.append(&2, String, Hs, cs), p))), BD.XK(cs))

law plan_k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +Hs: List<&2, String>
  for +e: Bool
  for +n1: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, Hs, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(Hs) && E.pieces_ok(Hs) == True{} : Bool}
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, Hs, cs)) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(VH(fa, T, cs, O, p, Hs), Nat.add(0n, 1n)), n1) == True{} : Bool}
  for r: &ps: List<&2, PT.Pc> -> ({W.plan.reqs_all(W.plan.all(PT.encs(Hs))) == (PT.mkPls(ps), PT.reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({PT.texts(ps) == Hs : List<&2, String>} & ({E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool} & PT.PcsOK(ps, cs))))
  API.KontW(fa, T, W.plan(S.mkSt(fa, p), PT.encs(Hs), e), cs, ef, 0n, n1, O, N)

def plan_k(fa, T, cs, O, N, ef, p, Hs, e, n1, hb, hm, hst, hg, hr, hby, he, hbi, hn, r):
  (+ps, r1) = r
  (+eq1, r2) = r1
  (+eq2, r3) = r2
  (hq, hps) = r3
  +back = Equal.sym(List<&2, String>, PT.texts(ps), Hs, eq2)
  +hr2 = AB.subst(List<&2, String>, z => {S.report(fa, List.append(&2, String, z, cs), O, N, p) == T : R.Report}, Hs, PT.texts(ps), back, hr)
  +hby2 = AB.subst(List<&2, String>, z => {E.all_bytes(z) && E.pieces_ok(z) == True{} : Bool}, Hs, PT.texts(ps), back, hby)
  +hbi2 = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), List.append(&2, String, z, cs)) == True{} : Bool}, Hs, PT.texts(ps), back, hbi)
  +hn1 = AB.subst(List<&2, String>, z => {Nat.is_le(Nat.add(VH(fa, T, cs, O, p, z), Nat.add(0n, 1n)), n1) == True{} : Bool}, Hs, PT.texts(ps), back, hn)
  +hn2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, Nat.add(1n+Nat.add(z, z), BDs.WP(fa, List.append(&2, String, PT.texts(ps), cs), p))), BD.XK(cs)), Nat.add(0n, 1n)), n1) == True{} : Bool},
    List.length(&2, String, PT.texts(ps)), List.length(&2, PT.Pc, ps), H1.len_texts(ps), hn1)
  %Equal.sym(List<&1, W.Pl> & List<&2, Pr.Req>, W.plan.reqs_all(W.plan.all(PT.encs(Hs))), (PT.mkPls(ps), PT.reqs_of(ps)), eq1) :
    API.KontW(fa, T, W.plan.ask(S.mkSt(fa, p), _, e), cs, ef, 0n, n1, O, N)
  plan_if(fa, T, cs, O, N, ef, p, ps, e, n1, hb, hm, hst, hg, hr2, hby2, he, hbi2, hn2, List.is_empty(&2, Pr.Req, PT.reqs_of(ps)), {==}, DU.pcsok_dup(ps, cs, hps))

# The step that closes a batch of the pieces Hs (in file order).
law plan_bud:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +Hs: List<&2, String>
  for +e: Bool
  for +n1: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, Hs, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(Hs) && E.pieces_ok(Hs) == True{} : Bool}
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, Hs, cs)) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(VH(fa, T, cs, O, p, Hs), Nat.add(0n, 1n)), n1) == True{} : Bool}
  API.KontW(fa, T, W.plan(S.mkSt(fa, p), PT.encs(Hs), e), cs, ef, 0n, n1, O, N)

def plan_bud(fa, T, cs, O, N, ef, p, Hs, e, n1, hb, hm, hst, hg, hr, hby, he, hbi, hn):
  plan_k(fa, T, cs, O, N, ef, p, Hs, e, n1, hb, hm, hst, hg, hr, hby, he, hbi, hn,
    PT.plan_all(Hs, cs, PB.and_true_l(E.all_bytes(Hs), E.pieces_ok(Hs), hby), PB.and_true_r(E.all_bytes(Hs), E.pieces_ok(Hs), hby)))
