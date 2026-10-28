import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm.bend as Norm
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_cache.bend as PCA
import ./MACHINE.bend as M
import ./proof_b_simdefs.bend as S
import ./proof_b_lines.bend as PL
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_pump.bend as DP
import ./proof_b_frame_fr.bend as FR
import ./proof_base.bend as PB
import ./proof_machine_nat.bend as PN
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-words/proof_nat.bend as N

# Helpers for proof_b_drive.bend: one driver input (a piece, the end of the
# file) given to a state waiting for more, then go: the fuel go computes is
# the state's measure (plus one in the String mode), so pump_ok applies.

# go
# ==

law fuel_eq:
  for +sps: List<&2, P.SrcP>
  {Norm.fuel.src(P.mkSrcs(sps)) == (P.mkSrcs(sps), S.msrc(sps)) : List<&1, Norm.Src> & Nat}

def fuel_eq(sps):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(rest)), (P.mkSrcs(rest), S.msrc(rest)), fuel_eq(rest)) :
        {Norm.fuel.cons((Norm.SB{C.BT(len, t), at}, (len - at : U32)), _) == (P.mkSrc(P.SBP{len, t, d, at}) <> P.mkSrcs(rest), S.msrc(P.SBP{len, t, d, at} <> rest)) : List<&1, Norm.Src> & Nat}
      {==}
    case Con{P.SLP{+q}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(rest)), (P.mkSrcs(rest), S.msrc(rest)), fuel_eq(rest)) :
        {Norm.fuel.cons((Norm.SL{q}, 0), _) == (Norm.SL{q} <> P.mkSrcs(rest), S.msrc(P.SLP{q} <> rest)) : List<&1, Norm.Src> & Nat}
      {==}

law meas_le:
  for +md: S.MdP
  for +o: B.Opts
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {Nat.is_le(S.measure(S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), Nat.add(S.msrc(src), 1n)) == True{} : Bool}

def meas_le(md, o, src, pd, eof, back, wp, asked, fneed):
  match md:
    case S.MBP{+rp}:
      N.le_refl(Nat.add(S.msrc(src), 1n))
    case S.MSP{+s, +qs, +ql, +code}:
      N.le_add_r(S.msrc(src), 1n)

# go from a good state: the pump with fuel for every line.
law go_ok2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  DO.StepG2(fa, T, cs, O, N, S.StP.eof(p), Norm.go(S.mkSt(fa, p)))

def go_ok2(fa, T, cs, O, N, p, hb, hw, hr, ha, hg):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(src)), (P.mkSrcs(src), S.msrc(src)), fuel_eq(src)) :
        DO.StepG2(fa, T, cs, O, N, eof, Norm.go.k(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed))
      DP.pump_ok_h2(fa, T, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}, Nat.add(S.msrc(src), 1n), hb, hw, hr, ha, hg,
        meas_le(md, o, src, pd, eof, back, wp, asked, fneed))


law go_ok:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  DR.StepG(fa, T, cs, O, N, Norm.go(S.mkSt(fa, p)))

def go_ok(fa, T, cs, O, N, p, hb, hw, hr, ha, hg):
  DO.sg2w(fa, T, cs, O, N, S.StP.eof(p), Norm.go(S.mkSt(fa, p)), go_ok2(fa, T, cs, O, N, p, hb, hw, hr, ha, hg))

# Reports
# =======

# Two states with the same options and run whose texts still to come have the
# same lines stand for the same report.
law rep_lines:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +cs2: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +src2: List<&2, P.SrcP>
  for +pd2: P.PdP
  for +eof2: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +back2: Nat
  for +wp2: PC.WP
  for +asked2: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +fneed2: Bool
  for +hl: {B.Text.lines(S.intext(S.StP{o, md, src2, pd2, eof2, back2, wp2, asked2, fneed2}, cs2)) == B.Text.lines(S.intext(S.StP{o, md, src, pd, eof, back, wp, asked, fneed}, cs)) : List<&2, B.Line>}
  {S.report(fa, cs2, O, N, S.StP{o, md, src2, pd2, eof2, back2, wp2, asked2, fneed2}) == S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) : R.Report}

def rep_lines(fa, cs, cs2, O, N, o, md, src, pd, eof, src2, pd2, eof2, back, wp, asked, back2, wp2, asked2, fneed, fneed2, hl):
  match md:
    case S.MBP{+rp}:
      Equal.cong(List<&2, B.Line>, R.Report, z => R.finish(L.run.go(z, fa, o, S.pre(O, N, P.specRun(rp)))), B.Text.lines(S.intext(S.StP{o, S.MBP{rp}, src2, pd2, eof2, back2, wp2, asked2, fneed2}, cs2)), B.Text.lines(S.intext(S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}, cs)), hl)
    case S.MSP{+s, +qs, +ql, None{}}:
      Equal.cong(List<&2, B.Line>, R.Report, z => R.finish(L.run.go(z, fa, o, S.pre(O, N, S.with_out(s, Norm.cat(List.reverse(&2, String, qs)))))), B.Text.lines(S.intext(S.StP{o, S.MSP{s, qs, ql, None{}}, src2, pd2, eof2, back2, wp2, asked2, fneed2}, cs2)), B.Text.lines(S.intext(S.StP{o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed}, cs)), hl)
    case S.MSP{+s, +qs, +ql, Some{+c}}:
      {==}

# Bool and String facts
# =====================

law empty_of_len:
  for +s: String
  for +h: {Nat.is_eq(String.length(s), 0n) == True{} : Bool}
  {String.is_empty(s) == True{} : Bool}

def empty_of_len(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({String.is_empty(SCon{c, t}) == True{} : Bool}, PB.false_ne_true(h))

law nonempty_of_len:
  for +s: String
  for +h: {Nat.is_eq(String.length(s), 0n) == False{} : Bool}
  {String.is_empty(s) == False{} : Bool}

def nonempty_of_len(s, h):
  match s:
    case SNil{}:
      Empty.absurd({String.is_empty("") == False{} : Bool}, PB.true_ne_false(h))
    case SCon{c, t}:
      {==}

law rev_app:
  for +x: String
  for +y: String
  for +acc: String
  {String.reverse.go(String.append(x, y), acc) == String.reverse.go(y, String.reverse.go(x, acc)) : String}

def rev_app(x, y, acc):
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rev_app(t, y, SCon{h, acc})

# A text with a final LF ends with one.
law ends_lf_lf:
  for +x: String
  {S.ends_lf(String.append(x, "\n")) == True{} : Bool}

def ends_lf_lf(x):
  %Equal.sym(String, String.reverse.go(String.append(x, "\n"), ""), String.reverse.go("\n", String.reverse.go(x, "")), rev_app(x, "\n", "")) :
    {Bool.or(String.is_empty(String.append(x, "\n")), String.starts_with(_, String.reverse("\n"))) == True{} : Bool}
  FR.or_true_r(String.is_empty(String.append(x, "\n")))

# The end of the file
# ===================

law eof_empty:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +he: {String.is_empty(P.pdtext(pd)) == True{} : Bool}
  DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.go(S.mkSt(fa, S.StP{o, md, Nil{}, pd, True{}, back, wp, None{}, fneed})))

def eof_empty(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, he):
  +hw1 = DO.x9_mk(S.md_ok(md), True{}, P.pd_ok(pd), P.nolf(P.pdtext(pd)), True{}, Bool.and(String.is_empty(P.pdtext(pd)), True{}), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)),
    DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), {==}, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), {==},
    %Equal.sym(Bool, String.is_empty(P.pdtext(pd)), True{}, he) : {Bool.and(_, True{}) == True{} : Bool}; {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p1 = {S.StP{o, md, Nil{}, pd, True{}, back, wp, None{}, fneed} : S.StP}
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  go_ok2(fa, T, Nil{}, O, N, p1, hb, hw1,
    Equal.trans(R.Report, S.report(fa, Nil{}, O, N, p1), S.report(fa, Nil{}, O, N, p0), T,
      rep_lines(fa, Nil{}, Nil{}, O, N, o, md, Nil{}, pd, False{}, Nil{}, pd, True{}, back, wp, None{}, back, wp, None{}, fneed, fneed, {==}), hr),
    {==}, hg)

# The last line's text, given its LF, has the same lines.
law lines_eof2:
  for +X: String
  for +st: String
  for +pt: String
  for +hst: {st == String.append(X, "\n") : String}
  for +hpt: {pt == "" : String}
  for +hn: {P.nolf(X) == True{} : Bool}
  for +hx: {String.is_empty(X) == False{} : Bool}
  {B.Text.lines(String.append(String.append(st, ""), String.append(pt, ""))) == B.Text.lines(String.append(X, "")) : List<&2, B.Line>}

def lines_eof2(X, st, pt, hst, hpt, hn, hx):
  %Equal.sym(String, st, String.append(X, "\n"), hst) :
    {B.Text.lines(String.append(String.append(_, ""), String.append(pt, ""))) == B.Text.lines(String.append(X, "")) : List<&2, B.Line>}
  %Equal.sym(String, pt, "", hpt) :
    {B.Text.lines(String.append(String.append(String.append(X, "\n"), ""), String.append(_, ""))) == B.Text.lines(String.append(X, "")) : List<&2, B.Line>}
  %Equal.sym(String, String.append(String.append(String.append(X, "\n"), ""), ""), String.append(String.append(X, "\n"), ""), PN.str_nil(String.append(String.append(X, "\n"), ""))) :
    {B.Text.lines(_) == B.Text.lines(String.append(X, "")) : List<&2, B.Line>}
  %Equal.sym(String, String.append(String.append(X, "\n"), ""), String.append(X, "\n"), PN.str_nil(String.append(X, "\n"))) :
    {B.Text.lines(_) == B.Text.lines(String.append(X, "")) : List<&2, B.Line>}
  %Equal.sym(String, String.append(X, ""), X, PN.str_nil(X)) :
    {B.Text.lines(String.append(X, "\n")) == B.Text.lines(_) : List<&2, B.Line>}
  PL.lines_eof("", X, hn, hx)

law b5_eof:
  for +X: String
  for +st: String
  for +pt: String
  for +hst: {st == String.append(X, "\n") : String}
  for +hpt: {pt == "" : String}
  {Bool.and(String.is_empty(pt), S.ends_lf(String.append(st, ""))) == True{} : Bool}

def b5_eof(X, st, pt, hst, hpt):
  %Equal.sym(String, pt, "", hpt) : {Bool.and(String.is_empty(_), S.ends_lf(String.append(st, ""))) == True{} : Bool}
  %Equal.sym(String, String.append(st, ""), st, PN.str_nil(st)) : {Bool.and(True{}, S.ends_lf(_)) == True{} : Bool}
  %Equal.sym(String, st, String.append(X, "\n"), hst) : {Bool.and(True{}, S.ends_lf(_)) == True{} : Bool}
  ends_lf_lf(X)

law eof_full2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +sp: P.SrcP
  for +pp0: P.PdP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hne: {String.is_empty(P.pdtext(pd)) == False{} : Bool}
  for +e1: {Norm.eof_src(P.mkPd(pd)) == P.mkSrc(sp) : Norm.Src}
  for +hso: {P.src_ok(sp) == True{} : Bool}
  for +hst: {P.srctext(sp) == String.append(P.pdtext(pd), "\n") : String}
  for +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp0) : Norm.Pd}
  for +hpo: {P.pd_ok(pp0) == True{} : Bool}
  for +hpt: {P.pdtext(pp0) == "" : String}
  DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.go(Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.eof_src(P.mkPd(pd))]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed}))

def eof_full2(fa, T, O, N, o, md, pd, back, wp, fneed, sp, pp0, hb, hw, hr, hg, hne, e1, hso, hst, f1, hpo, hpt):
  %Equal.sym(Norm.Src, Norm.eof_src(P.mkPd(pd)), P.mkSrc(sp), e1) :
    DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.go(Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [_]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed}))
  %Equal.sym(Norm.Pd, Norm.PB{BY.empty(0n)}, P.mkPd(pp0), f1) :
    DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.go(Norm.St{o, S.mkMd(md), [P.mkSrc(sp)], _, True{}, back, PC.mkWin(fa, wp), None{}, fneed}))
  +X = P.pdtext(pd)
  +hw2 = DO.x9_mk(S.md_ok(md), P.src_ok(sp), P.pd_ok(pp0), P.nolf(P.pdtext(pp0)), String.is_empty(P.pdtext(pp0)),
    Bool.and(String.is_empty(P.pdtext(pp0)), S.ends_lf(String.append(P.srctext(sp), ""))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)),
    DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hso, hpo,
    %Equal.sym(String, P.pdtext(pp0), "", hpt) : {P.nolf(_) == True{} : Bool}; {==},
    %Equal.sym(String, P.pdtext(pp0), "", hpt) : {String.is_empty(_) == True{} : Bool}; {==},
    b5_eof(X, P.srctext(sp), P.pdtext(pp0), hst, hpt),
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p2 = {S.StP{o, md, [sp], pp0, True{}, back, wp, None{}, fneed} : S.StP}
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  go_ok2(fa, T, Nil{}, O, N, p2, hb, hw2,
    Equal.trans(R.Report, S.report(fa, Nil{}, O, N, p2), S.report(fa, Nil{}, O, N, p0), T,
      rep_lines(fa, Nil{}, Nil{}, O, N, o, md, Nil{}, pd, False{}, [sp], pp0, True{}, back, wp, None{}, back, wp, None{}, fneed, fneed,
        lines_eof2(X, P.srctext(sp), P.pdtext(pp0), hst, hpt, DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hne)), hr),
    {==}, hg)

law eof_full:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hne: {String.is_empty(P.pdtext(pd)) == False{} : Bool}
  for eo: &sp: P.SrcP -> ({Norm.eof_src(P.mkPd(pd)) == P.mkSrc(sp) : Norm.Src} & ({P.src_ok(sp) == True{} : Bool} & {P.srctext(sp) == String.append(P.pdtext(pd), "\n") : String}))
  for pe: &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd} & ({P.pd_ok(pp) == True{} : Bool} & {P.pdtext(pp) == "" : String}))
  DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.go(Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.eof_src(P.mkPd(pd))]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed}))

def eof_full(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hne, eo, pe):
  (+sp, eo1) = eo
  (+e1, eo2) = eo1
  (hso, hst) = eo2
  (+pp0, pe1) = pe
  (+f1, pe2) = pe1
  (hpo, hpt) = pe2
  eof_full2(fa, T, O, N, o, md, pd, back, wp, fneed, sp, pp0, hb, hw, hr, hg, hne, e1, hso, hst, f1, hpo, hpt)

law eof_if:
  for +c: Bool
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hc: {Nat.is_eq(String.length(P.pdtext(pd)), 0n) == c : Bool}
  DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.go(Norm.feed_eof.if(c, o, S.mkMd(md), Nil{}, P.mkPd(pd), back, PC.mkWin(fa, wp), None{}, fneed)))

def eof_if(c, fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hc):
  match c:
    case True{}:
      eof_empty(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, empty_of_len(P.pdtext(pd), hc))
    case False{}:
      +hp = DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)
      eof_full(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, nonempty_of_len(P.pdtext(pd), hc), PL.eof_ok(pd, hp, DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)), PL.pd_empty())

# more_ok's four tests.
def M3(+w: Bool, +se: Bool, +ne: Bool) -> Bool:
  w && se && ne

law mo_se:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {se == True{} : Bool}

def mo_se(w, se, ne, no, h):
  PB.and_true_r(w, se, PB.and_true_l(Bool.and(w, se), ne, PB.and_true_l(M3(w, se, ne), no, h)))

law mo_ne:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {ne == True{} : Bool}

def mo_ne(w, se, ne, no, h):
  PB.and_true_r(Bool.and(w, se), ne, PB.and_true_l(M3(w, se, ne), no, h))

law mo_no:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {no == True{} : Bool}

def mo_no(w, se, ne, no, h):
  PB.and_true_r(M3(w, se, ne), no, h)

law mo_w:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {w == True{} : Bool}

def mo_w(w, se, ne, no, h):
  PB.and_true_l(w, se, PB.and_true_l(Bool.and(w, se), ne, PB.and_true_l(M3(w, se, ne), no, h)))

# step_eof with the step's eof flag (StepG2).
law step_eof_h2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, p), Pr.Eof{}))

def step_eof_h2(fa, T, O, N, p, hb, hm, hr, hg):
  match p:
    case S.StP{+o, +md, Con{+x, +t}, +pd, +eof, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Con{x, t}, pd, eof, back, wp, asked, fneed} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, q), Pr.Eof{})),
        PB.false_ne_true(mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, q), Pr.Eof{})),
        PB.false_ne_true(mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, q), Pr.Eof{})),
        PB.false_ne_true(mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
      +hw = mo_w(S.WF(fa, q), True{}, True{}, True{}, hm)
      +hp = DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)
      %Equal.sym(Norm.Pd & Nat, Norm.Pd.len(P.mkPd(pd)), (P.mkPd(pd), String.length(P.pdtext(pd))), PL.pd_len(pd, hp)) :
        DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.go(Norm.feed_eof.k(o, S.mkMd(md), Nil{}, _, back, PC.mkWin(fa, wp), None{}, fneed)))
      eof_if(Nat.is_eq(String.length(P.pdtext(pd)), 0n), fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, {==})

# step_eof, as proof_b_drive.bend states it.
law step_eof_h:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  DR.StepG(fa, T, Nil{}, O, N, Norm.step(S.mkSt(fa, p), Pr.Eof{}))

def step_eof_h(fa, T, O, N, p, hb, hm, hr, hg):
  DO.sg2w(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, p), Pr.Eof{}), step_eof_h2(fa, T, O, N, p, hb, hm, hr, hg))

# A reference answer
# ==================

# The window a read gives keeps mb_win: in the byte mode, a WPKnown window's
# contig is the reads' contig, bytes with at most 2^28 of them (mb_reqs).
law mbw_z:
  for +z: Bool
  for +c: String
  for +a: Nat
  for +b: Nat
  for +h: {Bool.and(E.is_bytes(c), Norm.len_le(c, 268435456)) == True{} : Bool}
  {S.mb_win.k(Bool.pick(PC.WP, z, PC.WPKnown{c, a, b}, PC.WPStr{c, a, b})) == True{} : Bool}

def mbw_z(z, c, a, b, h):
  match z:
    case True{}:
      h
    case False{}:
      {==}

law mbw_k:
  for +m: Maybe<&2, String>
  for +c: String
  for +a: Nat
  for +b: Nat
  for +h: {Bool.and(E.is_bytes(c), Norm.len_le(c, 268435456)) == True{} : Bool}
  {S.mb_win.k(PC.wpOf.k(m, c, a, b)) == True{} : Bool}

def mbw_k(m, c, a, b, h):
  match m:
    case None{}:
      {==}
    case Some{+r}:
      mbw_z(Norm.le31(Nat.sub(b, a)), c, a, b, h)

law mbw_of:
  for +md: S.MdP
  for +fa: List<&2, B.Contig>
  for +c: String
  for +a: Nat
  for +b0: Nat
  for +t: List<&2, Pr.Req>
  for +b: Nat
  for +h: {S.mb_reqs(md, Con{Pr.Req{c, a, b0}, t}) == True{} : Bool}
  {S.mb_win(md, PC.wpOf(fa, c, a, b)) == True{} : Bool}

def mbw_of(md, fa, c, a, b0, t, b, h):
  match md:
    case S.MBP{+rp}:
      mbw_k(B.Fasta.find(fa, c), c, a, b, h)
    case S.MSP{+s, +qs, +ql, +code}:
      {==}

law ref_win:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +c: String
  for +a: Nat
  for +b: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hmw: {S.mb_win(md, PC.wpOf(fa, c, a, b)) == True{} : Bool}
  for wt: {Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))) == PC.mkWin(fa, PC.wpOf(fa, c, a, b)) : Norm.Win}
    & {PC.wp_ok(fa, PC.wpOf(fa, c, a, b)) == True{} : Bool}
  DO.StepG2(fa, T, cs, O, N, eof, Norm.go(Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))), None{}, fneed}))

def ref_win(fa, T, cs, O, N, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, hb, hw, hr, hg, hmw, wt):
  (+wt1, wt2) = wt
  %Equal.sym(Norm.Win, Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))), PC.mkWin(fa, PC.wpOf(fa, c, a, b)), wt1) :
    DO.StepG2(fa, T, cs, O, N, eof, Norm.go(Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, _, None{}, fneed}))
  +hw2 = DO.x9_mk(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
    Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, PC.wpOf(fa, c, a, b)), S.mb_win(md, PC.wpOf(fa, c, a, b)), E.all_bytes(S.opts_args(o)),
    DO.x8_a(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_1(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_2(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_3(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_4(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_5(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), wt2, hmw, DO.x9_8(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  go_ok2(fa, T, cs, O, N, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, b), None{}, fneed}, hb, hw2,
    Equal.trans(R.Report, S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, b), None{}, fneed}), S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), T,
      rep_lines(fa, cs, cs, O, N, o, md, src, pd, eof, src, pd, eof, back, wp, asked, back, PC.wpOf(fa, c, a, b), None{}, fneed, fneed, {==}), hr),
    {==}, hg)

# step_ref with the step's eof flag (StepG2).
law step_ref_h2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +rs: List<&2, Pr.Req>
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
  for +hq: {E.reqs_ok(rs) == True{} : Bool}
  for +hp: {rs == S.rq(rs) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  DO.StepG2(fa, T, cs, O, N, S.StP.eof(p), Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))

def step_ref_h2(fa, T, cs, O, N, p, rs, hb, hw, hr, ha, hq, hp, hmr, hg):
  match p rs:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed} Nil{}:
      %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, None{}, ha) :
        DO.StepG2(fa, T, cs, O, N, eof, Norm.go(Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.set_win.of(_, PC.mkWin(fa, wp), Nil{}), None{}, fneed}))
      go_ok2(fa, T, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed}, hb, hw,
        Equal.trans(R.Report, S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed}), S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), T,
          rep_lines(fa, cs, cs, O, N, o, md, src, pd, eof, src, pd, eof, back, wp, asked, back, wp, None{}, fneed, fneed, {==}), hr),
        {==}, hg)
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed} Con{Pr.Req{+c, +a, +b}, +t}:
      +rs1 = {Con{Pr.Req{c, a, b}, t} : List<&2, Pr.Req>}
      +bb = Norm.last_b(t, b)
      %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, Some{rs1}, ha) :
        DO.StepG2(fa, T, cs, O, N, eof, Norm.go(Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.set_win.of(_, PC.mkWin(fa, wp), M.truths(fa, rs1)), None{}, fneed}))
      %Equal.sym(List<&2, Pr.Req>, rs1, Norm.parts(c, a, bb), hp) :
        DO.StepG2(fa, T, cs, O, N, eof, Norm.go(Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.win_of(_, M.truths(fa, _)), None{}, fneed}))
      ref_win(fa, T, cs, O, N, o, md, src, pd, eof, back, wp, asked, fneed, c, a, bb, hb, hw, hr, hg, mbw_of(md, fa, c, a, b, t, bb, hmr), PCA.win_truths(fa, c, a, bb, hb))

# step_ref, as proof_b_drive.bend states it.
law step_ref_h:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +rs: List<&2, Pr.Req>
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
  for +hq: {E.reqs_ok(rs) == True{} : Bool}
  for +hp: {rs == S.rq(rs) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  DR.StepG(fa, T, cs, O, N, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))

def step_ref_h(fa, T, cs, O, N, p, rs, hb, hw, hr, ha, hq, hp, hmr, hg):
  DO.sg2w(fa, T, cs, O, N, S.StP.eof(p), Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), step_ref_h2(fa, T, cs, O, N, p, rs, hb, hw, hr, ha, hq, hp, hmr, hg))

# A piece of the file
# ===================

# step_chunk from pb-lines' feed_ok (proof_b_drive_chunk.bend): feeding the
# piece c to a state waiting for more gives a good state p1 with nothing
# asked, standing for the same report with c no longer to come, and the same
# guard; go then pumps.
law step_chunk_go:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for fd: &p1: S.StP -> ({Norm.feed(S.mkSt(fa, p), E.enc(c)) == S.mkSt(fa, p1) : Norm.St}
    & ({S.WF(fa, p1) == True{} : Bool}
    & ({S.report(fa, cs, O, N, p1) == S.report(fa, c <> cs, O, N, p) : R.Report}
    & ({S.StP.asked(p1) == None{} : Maybe<&2, List<&2, Pr.Req>>}
    & {S.guard(O, N, p1) == S.guard(O, N, p) : Bool}))))
  DR.StepG(fa, T, cs, O, N, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}))

def step_chunk_go(fa, T, c, cs, O, N, p, hb, hr, hg, fd):
  (+p1, f1) = fd
  (+e1, f2) = f1
  (+hw1, f3) = f2
  (+er, f4) = f3
  (ha1, eg) = f4
  %Equal.sym(Norm.St, Norm.feed(S.mkSt(fa, p), E.enc(c)), S.mkSt(fa, p1), e1) : DR.StepG(fa, T, cs, O, N, Norm.go(_))
  go_ok(fa, T, cs, O, N, p1, hb, hw1,
    Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p), T, er, hr), ha1,
    Equal.trans(Bool, S.guard(O, N, p1), S.guard(O, N, p), True{}, eg, hg))
