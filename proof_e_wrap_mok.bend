import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as PRD
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_base.bend as PB
import ./proof_e_defs.bend as SD
import ./proof_e_task.bend as PT
import ./proof_e_merge.bend as MG
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_spec.bend as SP
import ./proof_e_wrap_edge.bend as ED
import ./proof_e_wrap_mg.bend as MR
import ./proof_e_wrap_seq.bend as WS
import ./proof_e_wrap_fb.bend as FB
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Helpers for proof_e_wrap.bend (area E1): a clean piece whose line across
# the boundary Q has handled (p3: one byte source at the piece's k+1, Q's
# count up by one): merge.ok holds and the task's run is spliced in (MOk),
# or not and Q goes on (MNo).

# The parts of a clean task's run fact (PT.TcOK's first test).
law tc_inv:
  for +fa: List<&2, B.Contig>
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +h: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}
  {PRD.RunInv(rpT) == True{} : Bool}

def tc_inv(fa, rpT, pdT, wpT, h):
  PB.and_true_l(PRD.RunInv(rpT), P.RunP.i(rpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT), Bool.not(P.RunP.x(rpT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)), P.pd_ok(pdT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT), P.nolf(P.pdtext(pdT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)), PC.wp_ok(fa, wpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT), S.mb_win(S.MBP{rpT}, wpT), h))))))

law tc_i:
  for +fa: List<&2, B.Contig>
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +h: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}
  {P.RunP.i(rpT) == True{} : Bool}

def tc_i(fa, rpT, pdT, wpT, h):
  PB.and_true_r(PRD.RunInv(rpT), P.RunP.i(rpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT), Bool.not(P.RunP.x(rpT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)), P.pd_ok(pdT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT), P.nolf(P.pdtext(pdT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)), PC.wp_ok(fa, wpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT), S.mb_win(S.MBP{rpT}, wpT), h))))))

law tc_nx:
  for +fa: List<&2, B.Contig>
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +h: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}
  {Bool.not(P.RunP.x(rpT)) == True{} : Bool}

def tc_nx(fa, rpT, pdT, wpT, h):
  PB.and_true_r(PRD.RunInv(rpT) && P.RunP.i(rpT), Bool.not(P.RunP.x(rpT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)), P.pd_ok(pdT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT), P.nolf(P.pdtext(pdT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)), PC.wp_ok(fa, wpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT), S.mb_win(S.MBP{rpT}, wpT), h)))))

law tc_pd:
  for +fa: List<&2, B.Contig>
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +h: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}
  {P.pd_ok(pdT) == True{} : Bool}

def tc_pd(fa, rpT, pdT, wpT, h):
  PB.and_true_r(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)), P.pd_ok(pdT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT), P.nolf(P.pdtext(pdT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)), PC.wp_ok(fa, wpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT), S.mb_win(S.MBP{rpT}, wpT), h))))

law tc_nl:
  for +fa: List<&2, B.Contig>
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +h: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}
  {P.nolf(P.pdtext(pdT)) == True{} : Bool}

def tc_nl(fa, rpT, pdT, wpT, h):
  PB.and_true_r(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT), P.nolf(P.pdtext(pdT)), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)), PC.wp_ok(fa, wpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT), S.mb_win(S.MBP{rpT}, wpT), h)))

law tc_wp:
  for +fa: List<&2, B.Contig>
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +h: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}
  {PC.wp_ok(fa, wpT) == True{} : Bool}

def tc_wp(fa, rpT, pdT, wpT, h):
  PB.and_true_r(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)), PC.wp_ok(fa, wpT), PB.and_true_l(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT), S.mb_win(S.MBP{rpT}, wpT), h))

law tc_mbw:
  for +fa: List<&2, B.Contig>
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +h: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}
  {S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool}

def tc_mbw(fa, rpT, pdT, wpT, h):
  PB.and_true_r(PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT), S.mb_win(S.MBP{rpT}, wpT), h)

# A true run that merge.ok accepts has not stopped (segok asks it).
law halt_of_segok:
  for +w: Nat
  for +c0: String
  for +l: Nat
  for +sx: R.RunSt
  for +tx: R.RunSt
  for +h: {SD.segok(w, c0, l, sx, tx) == True{} : Bool}
  {R.RunSt.halt(sx) == False{} : Bool}

def halt_of_segok(w, c0, l, sx, tx, h):
  match sx tx:
    case R.RunSt{+sn, True{}, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, True{}} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, +txx}:
      Empty.absurd({True{} == False{} : Bool}, PB.false_ne_true(h))
    case R.RunSt{+sn, False{}, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, True{}} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, +txx}:
      Empty.absurd({True{} == False{} : Bool}, PB.false_ne_true(h))
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, False{}} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, +txx}:
      {==}

# The records' conjunct of WF for a state with no source (option bytes only).
def w8_ab(+ab: Bool, +h: {ab == True{} : Bool}) -> {Bool.and(Bool.and(ab, True{}), True{}) == True{} : Bool}:
  %Equal.sym(Bool, ab, True{}, h) : {Bool.and(Bool.and(_, True{}), True{}) == True{} : Bool}
  {==}

# The state after the splice: Q's run is the merged one, its line end and
# window the task's, nothing else waiting; the batch goes on (Ask{[]}).
def mok_state(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o3: B.Opts,
  +c0: String, +rp2: P.RunP, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +dfs2: B.Defs,
  -src: List<&1, Norm.Src>, -pend: Norm.Pd, +back: Nat, -win: Norm.Win, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hout: {E.out(C.BT(P.RunP.obl(rp2), MG.RunP.obt(rp2))) == Some{P.obtext(rp2)} : Maybe<&2, String>},
  +hrep: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), String.append(O, P.obtext(rp2)), List.append(&2, B.Note, N, List.reverse(&2, B.Note, MG.RunP.ns(rp2))), S.StP{o3, S.MBP{MG.mergeP(c0, rp2, rpT)}, Nil{}, pdT, False{}, 0n, wpT, None{}, False{}, dfs2}) == T : R.Report},
  +hinv: {PRD.RunInv(MG.mergeP(c0, rp2, rpT)) == True{} : Bool},
  +hpd: {P.pd_ok(pdT) == True{} : Bool},
  +hnl: {P.nolf(P.pdtext(pdT)) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wpT) == True{} : Bool},
  +hmbw: {S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o3)) == True{} : Bool},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(dfs, fa, o3, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hdq: {S.DEFS(S.StP{o3, S.MBP{MG.mergeP(c0, rp2, rpT)}, Nil{}, pdT, False{}, 0n, wpT, None{}, False{}, dfs2}, List.append(&2, String, PT.texts(pt), cs)) == dfs : B.Defs}) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.comb.mg(W.MOk{C.BT(P.RunP.obl(rp2), MG.RunP.obt(rp2)), List.reverse(&2, B.Note, MG.RunP.ns(rp2)), P.mkRun(MG.mergeP(c0, rp2, rpT))}, o3, P.mkPd(pdT), PC.mkWin(fa, wpT), src, pend, back, win, asked, fneed, PT.mkTOuts(fa, pt, xt), e, dfs2)):
  +M = MG.mergeP(c0, rp2, rpT)
  +O2 = String.append(O, P.obtext(rp2))
  +N2 = List.append(&2, B.Note, N, List.reverse(&2, B.Note, MG.RunP.ns(rp2)))
  +hw = DO.x9_mk(S.md_ok(S.MBP{MG.mergeP(c0, rp2, rpT)}), S.srcs_ok(Nil{}), P.pd_ok(pdT), P.nolf(P.pdtext(pdT)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pdT))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pdT)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wpT), S.mb_win(S.MBP{MG.mergeP(c0, rp2, rpT)}, wpT), Bool.and(Bool.and(E.all_bytes(S.opts_args(o3)), S.recs_first(Nil{})), S.recs_run(S.MBP{MG.mergeP(c0, rp2, rpT)}, Nil{})), hinv, {==}, hpd, hnl, {==}, {==}, hwp, hmbw, w8_ab(E.all_bytes(S.opts_args(o3)), hab))
  +hib = Equal.trans(Bool, R.RunSt.inbody(P.specRun(M)), P.RunP.i(M), True{}, DO.ib_spec(M), MR.i_merge(c0, rp2, rpT))
  +hg = Equal.cong(Bool, Bool, z => Bool.or(z, Bool.and(String.is_empty(O2), List.is_empty(&2, B.Note, N2))), R.RunSt.inbody(P.specRun(M)), True{}, hib)
  (P.obtext(rp2), (WD.WPic{S.StP{o3, S.MBP{MG.mergeP(c0, rp2, rpT)}, Nil{}, pdT, False{}, 0n, wpT, None{}, False{}, dfs2}, WD.BCombP{pt, xt, e, False{}}}, (hout, ({==},
    (hdq, (hby, (hg, (hrep, ({==}, (DO.mo_mk(S.WF(fa, S.StP{o3, S.MBP{MG.mergeP(c0, rp2, rpT)}, Nil{}, pdT, False{}, 0n, wpT, None{}, False{}, dfs2}), True{}, True{}, True{}, hw, {==}, {==}, {==}), (MR.x_merge(c0, rp2, rpT), (hps, (hbo, he)))))))))))))


