import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_enc.bend as ENC
import ./proof_b_frame.bend as FM
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_base.bend as PB
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Helpers for proof_b_drive.bend: the end of the run (Norm.finish) from a
# good state with no lines left for the spec (the run stopped, or the file
# ended with nothing waiting) gives the report T.

# A state's report when no line is left: the stopped report.
def NoLines(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP) -> Data:
  {S.report(fa, cs, O, N, p) == R.finish(S.pre(O, N, S.smd(S.StP.md(p)))) : R.Report}

# Reports
# =======

# The driver's report is the spec's: run_finish's report, with O and N in
# front (finish_pre).
law rep_fin:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +a: String
  for +b: List<&2, B.Note>
  for +c: Nat
  for +hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}
  for +rf: {R.Report{a, b, c} == R.finish(st) : R.Report}
  {R.Report{String.append(O, a), List.append(&2, B.Note, N, b), c} == R.finish(S.pre(O, N, st)) : R.Report}

def rep_fin(O, N, st, a, b, c, hg, rf):
  %Equal.sym(R.Report, R.finish(S.pre(O, N, st)), R.Report{String.append(O, R.Report.out(R.finish(st))), List.append(&2, B.Note, N, R.Report.notes(R.finish(st))), R.Report.code(R.finish(st))}, FM.finish_pre(O, N, st, hg)) :
    {R.Report{String.append(O, a), List.append(&2, B.Note, N, b), c} == _ : R.Report}
  %rf : {R.Report{String.append(O, a), List.append(&2, B.Note, N, b), c} == R.Report{String.append(O, R.Report.out(_)), List.append(&2, B.Note, N, R.Report.notes(_)), R.Report.code(_)} : R.Report}
  {==}

# The byte mode
# =============

law fin_mb.k2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp2: P.RunP
  for +code: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hT: {R.Report{String.append(O, P.RunSt.out(P.specRun(rp2))), List.append(&2, B.Note, N, P.RunSt.notes(P.specRun(rp2))), code} == T : R.Report}
  for tk: DO.TakeR(rp2, DO.lsum(src))
  for +ef: Bool
  DO.StepG2(fa, T, cs, O, N, ef, Norm.out(S.mkSt(fa, S.StP{o, S.MBP{rp2}, src, pd, eof, back, wp, asked, fneed}), Pr.Finish{code}))

def fin_mb.k2(fa, T, cs, O, N, o, rp2, code, src, pd, eof, back, wp, asked, fneed, hT, tk, ef):
  (+ol, tk1) = tk
  (+ot, tk2) = tk1
  (+d, tk3) = tk2
  (+rp3, tk4) = tk3
  (+e1, tk5) = tk4
  (+eok, tk6) = tk5
  (+ech, tk7) = tk6
  (+einv, tk8) = tk7
  (+esp, eow) = tk8
  +t = P.RunSt.out(P.specRun(rp2))
  +ns = P.RunSt.notes(P.specRun(rp2))
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
    DO.StepG2(fa, T, cs, O, N, ef, Norm.out.left(o, Norm.MB{P.mkRun(rp2)}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Finish{code}))
  %Equal.sym((D.Bytes & List<&2, B.Note>) & NR.Run, NR.take(P.mkRun(rp2), DO.lsum(src)), ((C.BT(ol, ot), ns), P.mkRun(rp3)), e1) :
    DO.StepG2(fa, T, cs, O, N, ef, Norm.out.k(Norm.md.take.k(_), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Finish{code}))
  +eout = Equal.trans(Maybe<&2, String>, E.out(C.BT(ol, ot)), Some{E.chars(D.view(C.BT(ol, ot)))}, Some{t},
    ENC.out_ok(ol, ot, d, eok, C.ok_d(ol, ot, d, eok)),
    Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(ol, ot))), t,
      Equal.trans(String, E.chars(D.view(C.BT(ol, ot))), NR.chars(D.view(C.BT(ol, ot))), t, DO.chars_nr(D.view(C.BT(ol, ot))), ech)))
  (t, (eout, hT))

law fin_mb.k1:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hg: {R.RunSt.inbody(P.specRun(rp)) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}
  for +hT: {R.finish(S.pre(O, N, P.specRun(rp))) == T : R.Report}
  for rf: &rp2: P.RunP -> &code: Nat -> ({NR.finish(P.mkRun(rp), R.Opts.w(o)) == (P.mkRun(rp2), code) : NR.Run & Nat}
    & ({PR.RunInv(rp2) == True{} : Bool}
    & {R.Report{P.RunSt.out(P.specRun(rp2)), P.RunSt.notes(P.specRun(rp2)), code} == R.finish(P.specRun(rp)) : R.Report}))
  for +ef: Bool
  DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed})))

def fin_mb.k1(fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hg, hT, rf, ef):
  (+rp2, rf1) = rf
  (+code, rf2) = rf1
  (+efin, rf3) = rf2
  (+hi2, erep) = rf3
  %Equal.sym(NR.Run & Nat, NR.finish(P.mkRun(rp), R.Opts.w(o)), (P.mkRun(rp2), code), efin) :
    DO.StepG2(fa, T, cs, O, N, ef, Norm.fin.mb(o, _, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed))
  fin_mb.k2(fa, T, cs, O, N, o, rp2, code, src, pd, eof, back, wp, asked, fneed,
    Equal.trans(R.Report, R.Report{String.append(O, P.RunSt.out(P.specRun(rp2))), List.append(&2, B.Note, N, P.RunSt.notes(P.specRun(rp2))), code},
      R.finish(S.pre(O, N, P.specRun(rp))), T,
      rep_fin(O, N, P.specRun(rp), P.RunSt.out(P.specRun(rp2)), P.RunSt.notes(P.specRun(rp2)), code, hg, erep), hT),
    PR.run_take(rp2, DO.lsum(src), hi2), ef)

# The end of the run in the byte mode, from a good state with no lines left.
law fin_mb:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}) == T : R.Report}
  for +hnl: NoLines(fa, cs, O, N, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed})
  for +ef: Bool
  DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed})))

def fin_mb(fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hw, hg, hr, hnl, ef):
  +p = {S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed} : S.StP}
  fin_mb.k1(fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hg,
    Equal.trans(R.Report, R.finish(S.pre(O, N, P.specRun(rp))), S.report(fa, cs, O, N, p), T,
      Equal.sym(R.Report, S.report(fa, cs, O, N, p), R.finish(S.pre(O, N, P.specRun(rp))), hnl), hr),
    PR.run_finish(rp, o, DO.wf_md(fa, p, hw)), ef)

# No lines left
# =============

law halt_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  {R.RunSt.halt(S.pre(O, N, st)) == R.RunSt.halt(st) : Bool}

def halt_pre(O, N, st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law halt_spec:
  for +rp: P.RunP
  {R.RunSt.halt(P.specRun(rp)) == P.RunP.x(rp) : Bool}

def halt_spec(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# A stopped byte run: the spec's run over what is left changes nothing.
law nl_halt:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hx: {P.RunP.x(rp) == True{} : Bool}
  NoLines(fa, cs, O, N, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed})

def nl_halt(fa, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hx):
  +st = S.pre(O, N, P.specRun(rp))
  +hh = Equal.trans(Bool, R.RunSt.halt(st), R.RunSt.halt(P.specRun(rp)), True{}, halt_pre(O, N, P.specRun(rp)),
    Equal.trans(Bool, R.RunSt.halt(P.specRun(rp)), P.RunP.x(rp), True{}, halt_spec(rp), hx))
  +ls = B.Text.lines(S.intext(S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}, cs))
  Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(ls, fa, o, st), st, FM.run_halted(ls, fa, o, st, hh))

law str_empty:
  for +s: String
  for +h: {String.is_empty(s) == True{} : Bool}
  {s == "" : String}

def str_empty(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({SCon{c, t} == "" : String}, PB.false_ne_true(h))

# At the end of the file with no source, a good state's line end is empty.
law pd_eof:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed}) == True{} : Bool}
  {P.pdtext(pd) == "" : String}

def pd_eof(fa, o, md, pd, back, wp, asked, fneed, hw):
  +hb5 = DO.x9_5(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))),
    Bool.or(Bool.not(True{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)
  str_empty(P.pdtext(pd), PB.and_true_l(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})), hb5))

# Idle at the end of the file (byte mode): no line is left.
law nl_eof_mb:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, True{}, back, wp, asked, fneed}) == True{} : Bool}
  NoLines(fa, cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, True{}, back, wp, asked, fneed})

def nl_eof_mb(fa, cs, O, N, o, rp, pd, back, wp, asked, fneed, hw):
  %Equal.sym(String, P.pdtext(pd), "", pd_eof(fa, o, S.MBP{rp}, pd, back, wp, asked, fneed, hw)) :
    {R.finish(L.run.go(B.Text.lines(String.append("", String.append(_, ""))), fa, o, S.pre(O, N, P.specRun(rp)))) == R.finish(S.pre(O, N, P.specRun(rp))) : R.Report}
  {==}
