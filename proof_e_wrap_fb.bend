import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_b_drive_pump.bend as DP
import ./proof_base.bend as PB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_qx.bend as QX
import ./proof_e_wrap_seq.bend as WS
import ./proof_e_wrap_qd.bend as QD

# Helpers for proof_e_wrap.bend (area E1): a clean piece left to Q after the
# edge's advances: Q goes on (go), or its last advance asked for reads, was
# idle, ended or yielded; then the batch goes on (WS.seq_ok).

# Q goes on from a good state.
def go_seq(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p2: S.StP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw2: {S.WF(fa, p2) == True{} : Bool},
  +hr2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report},
  +ha2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hg2: {S.guard(O, N, p2) == True{} : Bool},
  +hef2: {S.StP.eof(p2) == False{} : Bool},
  +eo2: {S.StP.o(p2) == o : B.Opts},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(dfs, fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hdc: {S.DEFS(p2, List.append(&2, String, PT.texts(pt), cs)) == dfs : B.Defs}) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.go(S.mkSt(fa, p2)), PT.mkTOuts(fa, pt, xt), e)):
  +CS = List.append(&2, String, PT.texts(pt), cs)
  WS.seq_ok(dfs, fa, T, cs, O, N, ef, o, pt, xt, e, Norm.go(S.mkSt(fa, p2)),
    WB.g2_ef(fa, T, CS, O, N, S.StP.eof(p2), False{}, Norm.go(S.mkSt(fa, p2)), hef2, DS.go_ok2(fa, T, CS, O, N, p2, hb, hw2, hr2, ha2, hg2)),
    QX.xs_o(Norm.go(S.mkSt(fa, p2)), S.StP.o(p2), o, eo2, QX.go_x(fa, Nil{}, O, N, p2, hb, hw2, hg2)),
    hby, hps, hbo, he,
    QD.pd_rw(Norm.go(S.mkSt(fa, p2)), CS, S.DEFS(p2, CS), dfs, hdc, QD.go_d(fa, CS, O, N, p2, hb, hw2, hg2)))

# The edge's advance asked for reads: Q asks them.
def want_seq(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +pc: S.StP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, -st: Norm.St, +r: List<&2, Pr.Req>,
  +hefc: {S.StP.eof(pc) == False{} : Bool},
  +hoc: {S.StP.o(pc) == o : B.Opts},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(dfs, fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hdc: {S.DEFS(pc, List.append(&2, String, PT.texts(pt), cs)) == dfs : B.Defs},
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, Norm.Want{st, r})) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.pump(0n, Norm.Want{st, r}), PT.mkTOuts(fa, pt, xt), e)):
  (+p2, a1) = ag
  (est, a2) = a1
  (+wf2, a3) = a2
  (+er2, a4) = a3
  (+eq, a5) = a4
  (+erq, a6) = a5
  (+eask, a7) = a6
  (+ens, a8) = a7
  (+emr, a9) = a8
  (+eeof, a10) = a9
  (+eg, a11) = a10
  (eo, mvk) = a11
  (mv, kp) = mvk
  +CS = List.append(&2, String, PT.texts(pt), cs)
  %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.out(_, Pr.Ask{r}), PT.mkTOuts(fa, pt, xt), e))
  WS.seq_ok(dfs, fa, T, cs, O, N, ef, o, pt, xt, e, Norm.out(S.mkSt(fa, p2), Pr.Ask{r}),
    DO.out_ask(fa, T, CS, O, N, p2, r, Norm.out(S.mkSt(fa, p2), Pr.Ask{r}), DO.out_ok(fa, CS, O, N, p2, Pr.Ask{r}, wf2, eg, DO.live_of(S.StP.md(p2), ens)), er2, eq, erq, emr, eask,
      False{}, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefc)),
    QX.xs_o(Norm.out(S.mkSt(fa, p2), Pr.Ask{r}), WB.st_o(S.mkSt(fa, p2)), o, QX.ostep(fa, p2, o, Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hoc)), QX.out_xs(S.mkSt(fa, p2), Pr.Ask{r}, {==})),
    hby, hps, hbo, he, QD.dk_out(fa, p2, Pr.Ask{r}, CS, dfs, Equal.trans(B.Defs, S.DEFS(p2, CS), S.DEFS(pc, CS), dfs, QD.moved_defs(fa, CS, pc, p2, mv), hdc)))

# The edge's advance found no line: Q waits for more or ends.
def idle_seq(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +pc: S.StP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, -st: Norm.St,
  +hac: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefc: {S.StP.eof(pc) == False{} : Bool},
  +hoc: {S.StP.o(pc) == o : B.Opts},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(dfs, fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hdc: {S.DEFS(pc, List.append(&2, String, PT.texts(pt), cs)) == dfs : B.Defs},
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, Norm.Idle{st})) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.pump(0n, Norm.Idle{st}), PT.mkTOuts(fa, pt, xt), e)):
  (+p2, a1) = ag
  (est, a2) = a1
  (+wf2, a3) = a2
  (+er2, a4) = a3
  (+esrc, a5) = a4
  (+eask, a6) = a5
  (+eeof, a7) = a6
  (+ens, a8) = a7
  (+eg, a9) = a8
  (eo, mvk) = a9
  (mv, kp) = mvk
  +CS = List.append(&2, String, PT.texts(pt), cs)
  %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.idle(_), PT.mkTOuts(fa, pt, xt), e))
  WS.seq_ok(dfs, fa, T, cs, O, N, ef, o, pt, xt, e, Norm.idle(S.mkSt(fa, p2)),
    DP.idle_go(fa, T, CS, O, N, p2, wf2, er2, esrc, eg, ens, Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(pc), None{}, eask, hac),
      False{}, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefc)),
    QX.xs_o(Norm.idle(S.mkSt(fa, p2)), S.StP.o(p2), o, Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hoc), QX.idle_x(fa, p2, ens)),
    hby, hps, hbo, he, QD.idle_d(fa, p2, CS, dfs, Equal.trans(B.Defs, S.DEFS(p2, CS), S.DEFS(pc, CS), dfs, QD.moved_defs(fa, CS, pc, p2, mv), hdc)))

# The edge's advance stopped the run: Q ends it.
def ended_seq(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +pc: S.StP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, -st: Norm.St,
  +hac: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefc: {S.StP.eof(pc) == False{} : Bool},
  +hoc: {S.StP.o(pc) == o : B.Opts},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(dfs, fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hdc: {S.DEFS(pc, List.append(&2, String, PT.texts(pt), cs)) == dfs : B.Defs},
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, Norm.Ended{st})) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.pump(0n, Norm.Ended{st}), PT.mkTOuts(fa, pt, xt), e)):
  (+p2, a1) = ag
  (est, a2) = a1
  (+wf2, a3) = a2
  (+er2, a4) = a3
  (+eask, a5) = a4
  (+estop, a6) = a5
  (+eeof, a7) = a6
  (eg, a8) = a7
  (eo, dkp) = a8
  (+hdd, kp) = dkp
  +CS = List.append(&2, String, PT.texts(pt), cs)
  %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.finish(_), PT.mkTOuts(fa, pt, xt), e))
  WS.seq_ok(dfs, fa, T, cs, O, N, ef, o, pt, xt, e, Norm.finish(S.mkSt(fa, p2)),
    DP.ended_go(fa, T, CS, O, N, p2, wf2, er2, estop, eg, Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(pc), None{}, eask, hac),
      False{}, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefc)),
    QX.xs_o(Norm.finish(S.mkSt(fa, p2)), WB.st_o(S.mkSt(fa, p2)), o, QX.ostep(fa, p2, o, Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hoc)), QX.finish_x(S.mkSt(fa, p2))),
    hby, hps, hbo, he, QD.finish_d(fa, p2, CS, dfs, Equal.trans(B.Defs, S.DEFS(p2, CS), S.DEFS(pc, CS), dfs, hdd, hdc)))

# The edge's advance wrote enough for one step: Q ends the step.
def yield_seq(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +pc: S.StP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, -st: Norm.St,
  +hac: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefc: {S.StP.eof(pc) == False{} : Bool},
  +hoc: {S.StP.o(pc) == o : B.Opts},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(dfs, fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hdc: {S.DEFS(pc, List.append(&2, String, PT.texts(pt), cs)) == dfs : B.Defs},
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, Norm.Yield{st})) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.pump(0n, Norm.Yield{st}), PT.mkTOuts(fa, pt, xt), e)):
  (+p2, a1) = ag
  (est, a2) = a1
  (+wf2, a3) = a2
  (+er2, a4) = a3
  (+eask, a5) = a4
  (+ens, a6) = a5
  (+eeof, a7) = a6
  (eg, a8) = a7
  (eo, dkp) = a8
  (+hdd, kp) = dkp
  +CS = List.append(&2, String, PT.texts(pt), cs)
  %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(dfs, fa, T, cs, O, N, ef, W.seq_out(Norm.out(_, Pr.Ask{Nil{}}), PT.mkTOuts(fa, pt, xt), e))
  WS.seq_ok(dfs, fa, T, cs, O, N, ef, o, pt, xt, e, Norm.out(S.mkSt(fa, p2), Pr.Ask{Nil{}}),
    DO.out_ask(fa, T, CS, O, N, p2, Nil{}, Norm.out(S.mkSt(fa, p2), Pr.Ask{Nil{}}), DO.out_ok(fa, CS, O, N, p2, Pr.Ask{Nil{}}, wf2, eg, DO.live_of(S.StP.md(p2), ens)), er2, {==}, {==}, DO.mbr_nil(S.StP.md(p2)),
      Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(pc), None{}, eask, hac),
      False{}, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefc)),
    QX.xs_o(Norm.out(S.mkSt(fa, p2), Pr.Ask{Nil{}}), WB.st_o(S.mkSt(fa, p2)), o, QX.ostep(fa, p2, o, Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hoc)), QX.out_xs(S.mkSt(fa, p2), Pr.Ask{Nil{}}, {==})),
    hby, hps, hbo, he, QD.dk_out(fa, p2, Pr.Ask{Nil{}}, CS, dfs, Equal.trans(B.Defs, S.DEFS(p2, CS), S.DEFS(pc, CS), dfs, hdd, hdc)))
