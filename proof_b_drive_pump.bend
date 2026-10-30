import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SA
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_fin.bend as DF
import ./proof_b_drive_finms.bend as FMS
import ./proof_base.bend as PB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Helpers for proof_b_drive.bend: pump_ok. Norm.pump handles lines while
# advance says Went (each lowers S.measure, so the fuel never runs out), then
# ends the step: out with an Ask (Want, Yield), idle (Idle: More, or the end
# of the run at the end of the file), or finish (Ended).

# The end of the run
# ==================

law or_false:
  for +x: Bool
  for +h: {Bool.or(x, False{}) == True{} : Bool}
  {x == True{} : Bool}

def or_false(x, h):
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PB.false_ne_true(h))

# A stopped run (Ended) finishes with the report.
law ended_go:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +hs: {S.stopped(S.StP.md(p)) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(S.mkSt(fa, p)))

def ended_go(fa, T, cs, O, N, p, hw, hr, hs, hg, ha, ef, hef):
  match p:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      DF.fin_mb(fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hw, hg, hr,
        DF.nl_halt(fa, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hs), ef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, Some{+cc}}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      FMS.fin_ms_some(fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hw, hr, hg, ha, ef, hef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, None{}}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      FMS.fin_ms_none(fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, hw, hr, hg, ha,
        FMS.nl_halt_ms(fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, or_false(x, hs)), ef, hef)

# Idle: More before the end of the file, else the end of the run.
law idle_go:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +hsrc: {S.src_empty(S.StP.src(p)) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hns: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.idle(S.mkSt(fa, p)))

def idle_go(fa, T, cs, O, N, p, hw, hr, hsrc, hg, hns, ha, ef, hef):
  match p:
    case S.StP{+o, +md, +src, +pd, False{}, +back, +wp, +asked, +fneed}:
      +p2 = {S.StP{o, md, src, pd, False{}, back, wp, asked, fneed} : S.StP}
      DO.out_more(fa, T, cs, O, N, p2, Norm.out(S.mkSt(fa, p2), Pr.More{}), DO.out_ok(fa, cs, O, N, p2, Pr.More{}, hw, hg, DO.live_of(S.StP.md(p2), hns)), hr, hsrc, {==}, ha, ef, hef)
    case S.StP{+o, S.MBP{+rp}, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      DF.fin_mb(fa, T, cs, O, N, o, rp, Nil{}, pd, True{}, back, wp, asked, fneed, hw, hg, hr,
        DF.nl_eof_mb(fa, cs, O, N, o, rp, pd, back, wp, asked, fneed, hw), ef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, Some{+cc}}, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      FMS.fin_ms_some(fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, Nil{}, pd, True{}, back, wp, asked, fneed, hw, hr, hg, ha, ef, hef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, None{}}, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      FMS.fin_ms_none(fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, Nil{}, pd, True{}, back, wp, asked, fneed, hw, hr, hg, ha,
        FMS.nl_eof_ms(fa, cs, O, N, o, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, pd, back, wp, asked, fneed, hw), ef, hef)
    case S.StP{+o, +md, Con{+x, +t}, +pd, True{}, +back, +wp, +asked, +fneed}:
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, ef, Norm.idle(S.mkSt(fa, S.StP{o, md, Con{x, t}, pd, True{}, back, wp, asked, fneed}))), PB.false_ne_true(hsrc))

# The pump
# ========

law fuel_le:
  for +m2: Nat
  for +m: Nat
  for +f: Nat
  for +hlt: {Nat.is_lt(m2, m) == True{} : Bool}
  for +hf: {Nat.is_le(m, 1n+f) == True{} : Bool}
  {Nat.is_le(m2, f) == True{} : Bool}

def fuel_le(m2, m, f, hlt, hf):
  Equal.trans(Bool, Nat.is_le(m2, f), Nat.is_lt(m2, 1n+f), True{},
    Equal.sym(Bool, Nat.is_lt(m2, 1n+f), Nat.is_le(m2, f), N.lt_succ_iff(m2, f)),
    N.lt_le_trans(m2, m, 1n+f, hlt, hf))

law pump_go:
  for +f: Nat
  for a: Norm.Adv
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  for ag: S.AdvG(fa, T, cs, O, N, p, a)
  DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(1n+f, a))

def pump_go(f, a, fa, T, cs, O, N, p, hb, ha, hf, ef, hef, ag):
  match f a:
    case 0n Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (elt, a5) = a4
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(1n, Norm.Went{st})),
        AB.lt_zero_absurd(S.measure(p2), N.lt_le_trans(S.measure(p2), S.measure(p), 0n, elt, hf)))
    case 1n+g Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+elt, a5) = a4
      (eask2, a6) = a5
      (eeof, a7) = a6
      (eg2, a8) = a7
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(1n+g, Norm.advance(_)))
      pump_go(g, Norm.advance(S.mkSt(fa, p2)), fa, T, cs, O, N, p2, hb, eask2, fuel_le(S.measure(p2), S.measure(p), g, elt, hf),
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef),
        SA.adv_ok(fa, T, cs, O, N, p2, hb, wf2, er2, eg2))
    case _ Norm.Want{st, +r}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+eq, a5) = a4
      (+erq, a6) = a5
      (eask, a7) = a6
      (ens, a8) = a7
      (emr, a9) = a8
      (eeof, a10) = a9
      (eg, a11) = a10
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.out(_, Pr.Ask{r}))
      DO.out_ask(fa, T, cs, O, N, p2, r, Norm.out(S.mkSt(fa, p2), Pr.Ask{r}), DO.out_ok(fa, cs, O, N, p2, Pr.Ask{r}, wf2, eg, DO.live_of(S.StP.md(p2), ens)), er2, eq, erq, emr, eask,
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))
    case _ Norm.Idle{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+esrc, a5) = a4
      (eask, a6) = a5
      (eeof, a7) = a6
      (ens, a8) = a7
      (eg, a9) = a8
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.idle(_))
      idle_go(fa, T, cs, O, N, p2, wf2, er2, esrc, eg, ens, Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), None{}, eask, ha),
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))
    case _ Norm.Ended{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (eask, a5) = a4
      (+estop, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(_))
      ended_go(fa, T, cs, O, N, p2, wf2, er2, estop, eg, Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), None{}, eask, ha),
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))
    case _ Norm.Yield{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+eask, a5) = a4
      (ens, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.out(_, Pr.Ask{Nil{}}))
      DO.out_ask(fa, T, cs, O, N, p2, Nil{}, Norm.out(S.mkSt(fa, p2), Pr.Ask{Nil{}}), DO.out_ok(fa, cs, O, N, p2, Pr.Ask{Nil{}}, wf2, eg, DO.live_of(S.StP.md(p2), ens)), er2, {==}, {==}, DO.mbr_nil(S.StP.md(p2)),
        Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), None{}, eask, ha),
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))

# The pump with the step's eof flag and nothing asked in More (StepG2).
law pump_ok_h2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +f: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}
  DO.StepG2(fa, T, cs, O, N, S.StP.eof(p), Norm.pump(1n+f, Norm.advance(S.mkSt(fa, p))))

def pump_ok_h2(fa, T, cs, O, N, p, f, hb, hw, hr, ha, hg, hf):
  pump_go(f, Norm.advance(S.mkSt(fa, p)), fa, T, cs, O, N, p, hb, ha, hf, S.StP.eof(p), {==}, SA.adv_ok(fa, T, cs, O, N, p, hb, hw, hr, hg))

# pump_ok, as proof_b_drive.bend states it.
law pump_ok_h:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +f: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}
  DR.StepG(fa, T, cs, O, N, Norm.pump(1n+f, Norm.advance(S.mkSt(fa, p))))

def pump_ok_h(fa, T, cs, O, N, p, f, hb, hw, hr, ha, hg, hf):
  DO.sg2w(fa, T, cs, O, N, S.StP.eof(p), Norm.pump(1n+f, Norm.advance(S.mkSt(fa, p))), pump_ok_h2(fa, T, cs, O, N, p, f, hb, hw, hr, ha, hg, hf))
