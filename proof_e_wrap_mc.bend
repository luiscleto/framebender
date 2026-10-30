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
import ./proof_e_wrap_mok.bend as MK
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Helpers for proof_e_wrap.bend (area E1): merge_case, a clean piece whose line across
# the boundary Q has handled (p3: one byte source at the piece's k+1, Q's
# count up by one): merge.ok holds and the task's run is spliced in (MOk),
# or not and Q goes on (MNo).

# merge.ok decides (z): the splice, or Q goes on. (rp1: Q's run before the
# piece came; ls1, hl1, hs1: the chained Moved facts from the fed state p1.)
def merge_k(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP,
  +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat,
  +o3: B.Opts, +rp2: P.RunP, +len2: U32, +t2: AT.Tree<U32>, +d2: Nat, +at2: U32, +pd2: P.PdP, +back2: Nat, +wp2: PC.WP, +asked2: Maybe<&2, List<&2, Pr.Req>>, +fneed2: Bool,
  +p1: S.StP, +rp1: P.RunP, +ls1: List<&2, B.Line>, +z: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hw3: {S.WF(fa, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == True{} : Bool},
  +hr3: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == T : R.Report},
  +ha3: {S.StP.asked(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hg3: {S.guard(O, N, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == True{} : Bool},
  +eo3: {o3 == o : B.Opts},
  +hn: {P.RunP.n(rp2) == 1n+n0 : Nat},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == P.RunP.n(rp1) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hl1: {B.Text.lines(S.intext(p1, List.append(&2, String, PT.texts(pt), cs))) == List.append(&2, B.Line, ls1, B.Text.lines(S.intext(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, List.append(&2, String, PT.texts(pt), cs)))) : List<&2, B.Line>},
  +hs1: {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls1, fa, S.StP.o(p1), P.specRun(rp1))) : R.RunSt},
  +hz: {MG.okP(l, R.Opts.w(o3), c0, rp2, rpT) == z : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.mg(W.merge(P.mkRun(rp2), P.mkRun(rpT), l, R.Opts.w(o3), c0), o3, P.mkPd(pdT), PC.mkWin(fa, wpT), P.mkSrcs([P.SBP{len2, t2, d2, at2}]), P.mkPd(pd2), back2, PC.mkWin(fa, wp2), asked2, fneed2, PT.mkTOuts(fa, pt, xt), e)):
  match z:
    case False{}:
      %Equal.sym(W.Mg, W.merge(P.mkRun(rp2), P.mkRun(rpT), l, R.Opts.w(o3), c0), W.MNo{P.mkRun(rp2)}, MG.merge_no(l, R.Opts.w(o3), c0, rp2, rpT, hz)) :
        WD.StepGW(fa, T, cs, O, N, ef, W.comb.mg(_, o3, P.mkPd(pdT), PC.mkWin(fa, wpT), P.mkSrcs([P.SBP{len2, t2, d2, at2}]), P.mkPd(pd2), back2, PC.mkWin(fa, wp2), asked2, fneed2, PT.mkTOuts(fa, pt, xt), e))
      FB.go_seq(fa, T, cs, O, N, ef, o, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, pt, xt, e, hb, hw3, hr3, ha3, hg3, {==}, eo3, hby, hps, hbo, he)
    case True{}:
      +w3 = R.Opts.w(o3)
      +R2 = B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))
      +hs2 = DO.x8_a(S.md_ok(S.MBP{rp2}), S.srcs_ok([P.SBP{len2, t2, d2, at2}]), P.pd_ok(pd2), P.nolf(P.pdtext(pd2)), Bool.or(S.src_empty([P.SBP{len2, t2, d2, at2}]), String.is_empty(P.pdtext(pd2))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd2)), S.ends_lf(P.srcstext([P.SBP{len2, t2, d2, at2}])))), PC.wp_ok(fa, wp2), S.mb_win(S.MBP{rp2}, wp2), E.all_bytes(S.opts_args(o3)), hw3)
      +htT = MK.tc_inv(fa, rpT, pdT, wpT, hT7)
      +hsg = MG.merge_segok(l, w3, c0, rp2, rpT, hs2, htT, hz)
      +hx2 = Equal.trans(Bool, P.RunP.x(rp2), R.RunSt.halt(P.specRun(rp2)), False{}, Equal.sym(Bool, R.RunSt.halt(P.specRun(rp2)), P.RunP.x(rp2), SP.spec_halt(rp2)),
        MK.halt_of_segok(w3, c0, l, P.specRun(rp2), P.specRun(rpT), hsg))
      +hone = ED.one_line(fa, S.StP.o(p1), ls1, rp1, rp2, hs1, Equal.trans(Nat, P.RunP.n(rp2), 1n+n0, 1n+P.RunP.n(rp1), hn, Equal.cong(Nat, Nat, q => 1n+q, n0, P.RunP.n(rp1), hn0)), hx2)
      +hmv = Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs))), B.Text.lines(S.intext(p1, List.append(&2, String, PT.texts(pt), cs))), List.append(&2, B.Line, ls1, B.Text.lines(S.intext(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, List.append(&2, String, PT.texts(pt), cs)))),
        Equal.cong(String, List<&2, B.Line>, q => B.Text.lines(q), S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)), S.intext(p1, List.append(&2, String, PT.texts(pt), cs)), Equal.sym(String, S.intext(p1, List.append(&2, String, PT.texts(pt), cs)), S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)), hint1)), hl1)
      +EL = Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, List.append(&2, String, PT.texts(pt), cs))), B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))), List.append(&2, B.Line, lsT, R2),
        ED.edge_lines(fa, c, k, List.append(&2, String, PT.texts(pt), cs), p, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, ls1, a, hm, hc, hna, hmv, hone), hlT)
      +hr3b = Equal.trans(R.Report, R.finish(L.run.go(List.append(&2, B.Line, lsT, R2), fa, o3, S.pre(O, N, P.specRun(rp2)))), R.finish(L.run.go(B.Text.lines(S.intext(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, List.append(&2, String, PT.texts(pt), cs))), fa, o3, S.pre(O, N, P.specRun(rp2)))), T,
        Equal.cong(List<&2, B.Line>, R.Report, q => R.finish(L.run.go(q, fa, o3, S.pre(O, N, P.specRun(rp2)))), List.append(&2, B.Line, lsT, R2), B.Text.lines(S.intext(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, List.append(&2, String, PT.texts(pt), cs))), Equal.sym(List<&2, B.Line>, B.Text.lines(S.intext(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}, List.append(&2, String, PT.texts(pt), cs))), List.append(&2, B.Line, lsT, R2), EL)), hr3)
      +hfc = Equal.trans(Maybe<&2, String>, SD.first_chrom(List.append(&2, B.Line, lsT, R2)), SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))), Some{c0},
        Equal.cong(List<&2, B.Line>, Maybe<&2, String>, q => SD.first_chrom(q), List.append(&2, B.Line, lsT, R2), B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))), Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))), List.append(&2, B.Line, lsT, R2), hlT)), hfc0)
      +hsT3 = Equal.trans(R.RunSt, P.settle(P.specRun(rpT)), P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))), P.settle(L.run.go(lsT, fa, o3, SD.rs0(c0, l))), hsT,
        Equal.cong(B.Opts, R.RunSt, q => P.settle(L.run.go(lsT, fa, q, SD.rs0(c0, l))), o, o3, Equal.sym(B.Opts, o3, o, eo3)))
      +hrep = MR.mg_rep_k(fa, o3, c0, l, O, N, rp2, rpT, lsT, R2, T, hr3b, hfc, hsT3, hsg, MG.merge_spec(l, w3, c0, rp2, rpT, hs2, htT, hz), DO.not_true(P.RunP.x(rpT), MK.tc_nx(fa, rpT, pdT, wpT, hT7)))
      %Equal.sym(W.Mg, W.merge(P.mkRun(rp2), P.mkRun(rpT), l, w3, c0), W.MOk{C.BT(P.RunP.obl(rp2), MG.RunP.obt(rp2)), List.reverse(&2, B.Note, MG.RunP.ns(rp2)), P.mkRun(MG.mergeP(c0, rp2, rpT))}, MG.merge_yes(l, w3, c0, rp2, rpT, hz)) :
        WD.StepGW(fa, T, cs, O, N, ef, W.comb.mg(_, o3, P.mkPd(pdT), PC.mkWin(fa, wpT), P.mkSrcs([P.SBP{len2, t2, d2, at2}]), P.mkPd(pd2), back2, PC.mkWin(fa, wp2), asked2, fneed2, PT.mkTOuts(fa, pt, xt), e))
      MK.mok_state(fa, T, cs, O, N, ef, o3, c0, rp2, rpT, pdT, wpT, pt, xt, e, P.mkSrcs([P.SBP{len2, t2, d2, at2}]), P.mkPd(pd2), back2, PC.mkWin(fa, wp2), asked2, fneed2,
        MR.ob_out(rp2, hs2), hrep, MG.merge_inv(l, w3, c0, rp2, rpT, hs2, htT, hz),
        MK.tc_pd(fa, rpT, pdT, wpT, hT7), MK.tc_nl(fa, rpT, pdT, wpT, hT7), MK.tc_wp(fa, rpT, pdT, wpT, hT7), MK.tc_mbw(fa, rpT, pdT, wpT, hT7), DO.x9_8(S.md_ok(S.MBP{rp2}), S.srcs_ok([P.SBP{len2, t2, d2, at2}]), P.pd_ok(pd2), P.nolf(P.pdtext(pd2)), Bool.or(S.src_empty([P.SBP{len2, t2, d2, at2}]), String.is_empty(P.pdtext(pd2))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd2)), S.ends_lf(P.srcstext([P.SBP{len2, t2, d2, at2}])))), PC.wp_ok(fa, wp2), S.mb_win(S.MBP{rp2}, wp2), E.all_bytes(S.opts_args(o3)), hw3),
        hby, hps, WS.bok_o(fa, o, o3, pt, xt, cs, Equal.sym(B.Opts, o3, o, eo3), hbo), he)

# A clean piece after the edge: Q at p3 (one byte source, count up by one),
# the chain from the fed state p1.
def merge_case(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP,
  +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat,
  +o3: B.Opts, +rp2: P.RunP, +len2: U32, +t2: AT.Tree<U32>, +d2: Nat, +at2: U32, +pd2: P.PdP, +back2: Nat, +wp2: PC.WP, +asked2: Maybe<&2, List<&2, Pr.Req>>, +fneed2: Bool,
  +p1: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hw3: {S.WF(fa, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == True{} : Bool},
  +hr3: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == T : R.Report},
  +ha3: {S.StP.asked(S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hg3: {S.guard(O, N, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}) == True{} : Bool},
  +eo3: {o3 == o : B.Opts},
  +hn: {P.RunP.n(rp2) == 1n+n0 : Nat},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  hch: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2})) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.splice(S.mkSt(fa, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)):
  match p1:
    case S.StP{+o1, S.MSP{+s1, +qs1, +ql1, +cd1}, +sr1, +pdd1, +ef1, +bk1, +wpp1, +as1, +fn1}:
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.comb.splice(S.mkSt(fa, S.StP{o3, S.MBP{rp2}, [P.SBP{len2, t2, d2, at2}], pd2, False{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)), PB.false_ne_true(hch))
    case S.StP{+o1, S.MBP{+rp1}, +sr1, +pdd1, +ef1, +bk1, +wpp1, +as1, +fn1}:
      (+ls1, h1) = hch
      (hl1, hs1) = h1
      +q1 = {S.StP{o1, S.MBP{rp1}, sr1, pdd1, ef1, bk1, wpp1, as1, fn1} : S.StP}
      merge_k(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, o3, rp2, len2, t2, d2, at2, pd2, back2, wp2, asked2, fneed2,
        q1, rp1, ls1, MG.okP(l, R.Opts.w(o3), c0, rp2, rpT),
        hb, hm, hw3, hr3, ha3, hg3, eo3, hn, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he,
        hint1, hn0, ho1, hl1, hs1, {==})
