import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_base.bend as PB
import ./proof_e_task.bend as PT
import ./proof_e_qif.bend as QI
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_qx.bend as QX
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# Helpers for proof_e_wrap.bend (area E1): a step of Q while combining (a
# dirty piece, the answers to what Q asked, the end of a batch).
# (Generated from a source with an {WB.st_o(WB.step_st(s)) == o : B.Opts} & {WB.live_k(WB.step_nx(s), WB.st_stop(WB.step_st(s))) == True{} : Bool} macro, as proof_e_wrap_qx.bend.)

# Q's step while combining
# ========================

law bok_o:
  for +fa: List<&2, B.Contig>
  for +o1: B.Opts
  for +o2: B.Opts
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +cs: List<&2, String>
  for +he: {o1 == o2 : B.Opts}
  for h: PT.BatchOK(fa, o1, ps, xs, cs)
  PT.BatchOK(fa, o2, ps, xs, cs)

def bok_o(fa, o1, o2, ps, xs, cs, he, h):
  %he : PT.BatchOK(fa, _, ps, xs, cs)
  h

law none_of:
  for +m: Maybe<&2, List<&2, Pr.Req>>
  for +h: {Maybe.is_none(&2, List<&2, Pr.Req>, m) == True{} : Bool}
  {m == None{} : Maybe<&2, List<&2, Pr.Req>>}

def none_of(m, h):
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, List<&2, Pr.Req>>}, PB.false_ne_true(h))

# The More case of a Q step, when the batch has pieces left or the file ended.
law seq_more_k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +o: B.Opts
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +e: Bool
  for -st: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +t: String
  for +p2: S.StP
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +rep: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
  for +gd: {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
  for +hmo: {DR.more_ok(fa, p2) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p2)) == False{} : Bool}
  for +eo: {S.StP.o(p2) == o : B.Opts}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for hbo: PT.BatchOK(fa, o, ps, xs, cs)
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.Step{W.St{st, W.BComb{PT.mkTOuts(fa, ps, xs), e, False{}}}, b, ns, Pr.Ask{Nil{}}})

def seq_more_k(fa, T, cs, O, N, ef, o, ps, xs, e, st, b, ns, t, p2, eout, est, rep, gd, hmo, hst, eo, hby, hps, hbo, he):
  (t, (WD.WPic{p2, WD.BCombP{ps, xs, e, False{}}}, (eout, (Equal.cong(Norm.St, W.St, z => W.St{z, W.BComb{PT.mkTOuts(fa, ps, xs), e, False{}}}, st, S.mkSt(fa, p2), est),
    (hby, (gd, (rep, ({==}, (hmo, (hst, (hps, (bok_o(fa, o, S.StP.o(p2), ps, xs, cs, Equal.sym(B.Opts, S.StP.o(p2), o, eo), hbo), he))))))))))))

law seq_more:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +o: B.Opts
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +e: Bool
  for -st: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +t: String
  for +p2: S.StP
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +rep: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
  for +gd: {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
  for +hmo: {DR.more_ok(fa, p2) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p2)) == False{} : Bool}
  for +eo: {S.StP.o(p2) == o : B.Opts}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for hbo: PT.BatchOK(fa, o, ps, xs, cs)
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.seq.more(W.list_nil(PT.mkTOuts(fa, ps, xs)), e, st, b, ns))

def seq_more(fa, T, cs, O, N, ef, o, ps, xs, e, st, b, ns, t, p2, eout, est, rep, gd, hmo, hst, eo, hby, hps, hbo, he):
  match ps xs e:
    case Nil{} Nil{} False{}:
      (t, (WD.WPic{p2, WD.BNoneP{}}, (eout, (Equal.cong(Norm.St, W.St, z => W.St{z, W.BNone{}}, st, S.mkSt(fa, p2), est),
        ({==}, (gd, (rep, (hmo, he))))))))
    case Nil{} Nil{} True{}:
      seq_more_k(fa, T, cs, O, N, ef, o, Nil{}, Nil{}, True{}, st, b, ns, t, p2, eout, est, rep, gd, hmo, hst, eo, hby, hps, hbo, he)
    case Con{+x, +pt} Con{+y, +xt} +e:
      seq_more_k(fa, T, cs, O, N, ef, o, x <> pt, y <> xt, e, st, b, ns, t, p2, eout, est, rep, gd, hmo, hst, eo, hby, hps, hbo, he)
    case Nil{} Con{+y, +xt} +e:
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.seq.more(W.list_nil(PT.mkTOuts(fa, Nil{}, y <> xt)), e, st, b, ns)), hbo)
    case Con{+x, +pt} Nil{} +e:
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.seq.more(W.list_nil(PT.mkTOuts(fa, x <> pt, Nil{})), e, st, b, ns)), hbo)

# A step of Q while combining (Q given the batch's next piece, the answers to
# its reads, or nothing), then the batch goes on.
law seq_ok:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +o: B.Opts
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +e: Bool
  for s: Norm.Step
  for h2: DO.StepG2(fa, T, List.append(&2, String, PT.texts(ps), cs), O, N, False{}, s)
  for hx: {WB.st_o(WB.step_st(s)) == o : B.Opts} & {WB.live_k(WB.step_nx(s), WB.st_stop(WB.step_st(s))) == True{} : Bool}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for hbo: PT.BatchOK(fa, o, ps, xs, cs)
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.seq_out(s, PT.mkTOuts(fa, ps, xs), e))

def seq_ok(fa, T, cs, O, N, ef, o, ps, xs, e, s, h2, hx, hby, hps, hbo, he):
  match s:
    case Norm.Step{st, b, ns, Pr.More{}}:
      (+t, g1) = h2
      (+p2, g2) = g1
      (+eout, g3) = g2
      (+est, g4) = g3
      (wf, g5) = g4
      (+rep, g6) = g5
      (+gd, g7) = g6
      (+hmo, hef) = g7
      (+ho, hlv) = hx
      +hst = WB.stop_pic(fa, p2, st, est, DO.not_true(WB.st_stop(st), hlv))
      +eo = WB.o_pic(fa, p2, st, est, o, ho)
      seq_more(fa, T, cs, O, N, ef, o, ps, xs, e, st, b, ns, t, p2, eout, est, rep, gd, hmo, hst, eo, hby, hps, hbo, he)
    case Norm.Step{st, b, ns, Pr.Ask{+r}}:
      (+t, g1) = h2
      (+p2, g2) = g1
      (+eout, g3) = g2
      (+est, g4) = g3
      (+wf, g5) = g4
      (+rep, g6) = g5
      (+hq, g7) = g6
      (+hrq, g8) = g7
      (+hmr, g9) = g8
      (+hask, g10) = g9
      (+gd, heof) = g10
      (+ho, hlv) = hx
      +eo = WB.o_pic(fa, p2, st, est, o, ho)
      (t, (WD.WPic{p2, WD.BCombP{ps, xs, e, True{}}}, (eout, (Equal.cong(Norm.St, W.St, z => W.St{z, W.BComb{PT.mkTOuts(fa, ps, xs), e, True{}}}, st, S.mkSt(fa, p2), est),
        (hby, (gd, (rep, ((wf, (hq, (hrq, (hmr, (hask, heof))))), ({==}, (hps, (bok_o(fa, o, S.StP.o(p2), ps, xs, cs, Equal.sym(B.Opts, S.StP.o(p2), o, eo), hbo), he)))))))))))
    case Norm.Step{st, b, ns, Pr.Finish{+c}}:
      h2

# Q in the middle of a piece, given the answers to what it asked.
def seq_ref(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP, +ps: List<&2, PT.Pc>, +xs: List<&2, PT.TOutP>, +e: Bool, +rs: List<&2, Pr.Req>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report},
  +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  +hq: {E.reqs_ok(rs) == True{} : Bool},
  +hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  +hef: {S.StP.eof(p) == False{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool},
  hps: PT.PcsOK(ps, cs),
  hbo: PT.BatchOK(fa, S.StP.o(p), ps, xs, cs),
  he: WD.EofOK(e, ef, cs)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.step(W.St{S.mkSt(fa, p), W.BComb{PT.mkTOuts(fa, ps, xs), e, True{}}}, Pr.Ref{M.truths(fa, rs)})):
  +CS = List.append(&2, String, PT.texts(ps), cs)
  seq_ok(fa, T, cs, O, N, ef, S.StP.o(p), ps, xs, e, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}),
    WB.g2_ef(fa, T, CS, O, N, S.StP.eof(p), False{}, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), hef,
      DS.step_ref_h2(fa, T, CS, O, N, p, rs, hb, hw, hr, ha, hq, hp, hmr, hg)),
    QX.ref_x(fa, O, N, p, rs, hb, hw, ha, hq, hp, hmr, hg),
    hby, hps, hbo, he)

# The end of the file closed the batch: Q gets it.
law comb_eof:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +hef: {ef == True{} : Bool}
  for +hcs: {cs == Nil{} : List<&2, String>}
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.end(True{}, S.mkSt(fa, p)))

def comb_eof(fa, T, cs, O, N, ef, p, hb, hm, hg, hr, hef, hcs):
  %Equal.sym(List<&2, String>, cs, Nil{}, hcs) : WD.StepGW(fa, T, _, O, N, ef, W.comb.end(True{}, S.mkSt(fa, p)))
  %Equal.sym(Bool, ef, True{}, hef) : WD.StepGW(fa, T, Nil{}, O, N, _, W.comb.end(True{}, S.mkSt(fa, p)))
  WB.g2_none(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, p), Pr.Eof{}), DS.step_eof_h2(fa, T, O, N, p, hb, hm,
    Equal.trans(R.Report, S.report(fa, Nil{}, O, N, p), S.report(fa, cs, O, N, p), T,
      Equal.cong(List<&2, String>, R.Report, z => S.report(fa, z, O, N, p), Nil{}, cs, Equal.sym(List<&2, String>, cs, Nil{}, hcs)), hr), hg))

# The batch's last piece is done: the end of the file, or wait for more.
law comb_end:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.end(e, S.mkSt(fa, p)))

def comb_end(fa, T, cs, O, N, ef, p, e, hb, hm, hl, hg, hr, he):
  match e:
    case True{}:
      (hef, hcs) = he
      comb_eof(fa, T, cs, O, N, ef, p, hb, hm, hg, hr, hef, hcs)
    case False{}:
      +w = S.WF(fa, p)
      +se = S.src_empty(S.StP.src(p))
      +ne = Bool.not(S.StP.eof(p))
      +no = Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p))
      +heof = DO.not_true(S.StP.eof(p), WB.mo_ne(w, se, ne, no, hm))
      WB.g2_none(fa, T, cs, O, N, ef, Norm.out(S.mkSt(fa, p), Pr.More{}),
        DO.out_more(fa, T, cs, O, N, p, Norm.out(S.mkSt(fa, p), Pr.More{}), DO.out_ok(fa, cs, O, N, p, Pr.More{}, WB.mo_w(w, se, ne, no, hm), hg, DO.live_of(S.StP.md(p), hl)),
          hr, WB.mo_se(w, se, ne, no, hm), heof, none_of(S.StP.asked(p), WB.mo_no(w, se, ne, no, hm)),
          ef, Equal.trans(Bool, S.StP.eof(p), False{}, ef, heof, Equal.sym(Bool, ef, False{}, he))))

# A dirty piece: Q handles it.
law comb_dirty:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p) == T : R.Report}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}
  for hps: PT.PcsOK(pt, cs)
  for hbo: PT.BatchOK(fa, S.StP.o(p), pt, xt, cs)
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.piece(W.TDirty{}, S.mkSt(fa, p), C.BT(len, t), PT.mkTOuts(fa, pt, xt), e))

def comb_dirty(fa, T, cs, O, N, ef, p, c, pt, xt, e, len, t, d, hb, hm, hg, hr, hcb, hcn, hby, hok, hv, hps, hbo, he):
  seq_ok(fa, T, cs, O, N, ef, S.StP.o(p), pt, xt, e, Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)}),
    QI.step_chunk_pic(fa, T, c, List.append(&2, String, PT.texts(pt), cs), O, N, p, len, t, d, hb, hm, hr, hcb, hcn, hg, hok, hv),
    QX.chunk_x(fa, O, N, c, p, len, t, d, hb, hm, hg, hok, hv),
    hby, hps, hbo, he)
