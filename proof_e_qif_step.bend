import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm.bend as W
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_cache.bend as PCA
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_b_run.bend as RN
import ./proof_base.bend as PB
import ./proof_e_qif_fed.bend as F
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Phase E, area "qif": the deliverables of proof_e_qif.bend from the fed
# state (proof_e_qif_fed.bend): step_chunk (the room in the output buffer,
# the feed, then go_ok2), W.feed_line (the feed without the room) and the
# parts of set_win (step_ref_h2's, with the state it leads to named).

# From the fed state to the step
# ==============================

# The report a fed state stands for: the same as before, with c no longer to
# come (same run and options, same lines).
def rep_of(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +c: String, +p0: S.StP, +p1: S.StP,
  +hmd: {S.StP.md(p1) == S.StP.md(p0) : S.MdP},
  +ho: {S.StP.o(p1) == S.StP.o(p0) : B.Opts},
  +hi: {S.intext(p1, cs) == S.intext(p0, c <> cs) : String},
  +hdf: {S.StP.dfs(p1) == S.StP.dfs(p0) : B.Defs},
  +hrc: {S.recs(S.StP.src(p1)) == S.recs(S.StP.src(p0)) : List<&2, P.SrcP>}) ->
  {S.report(fa, cs, O, N, p1) == S.report(fa, c <> cs, O, N, p0) : R.Report}:
  match p0 p1:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, dfs} S.StP{+o1, +md1, +src1, +pd1, +eof1, +back1, +wp1, +asked1, +fneed1, +dfs1}:
      %Equal.sym(S.MdP, md1, md, hmd) : {S.report(fa, cs, O, N, S.StP{o1, _, src1, pd1, eof1, back1, wp1, asked1, fneed1, dfs1}) == S.report(fa, c <> cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) : R.Report}
      %Equal.sym(B.Opts, o1, o, ho) : {S.report(fa, cs, O, N, S.StP{_, md, src1, pd1, eof1, back1, wp1, asked1, fneed1, dfs1}) == S.report(fa, c <> cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) : R.Report}
      %Equal.sym(B.Defs, dfs1, dfs, hdf) : {S.report(fa, cs, O, N, S.StP{o, md, src1, pd1, eof1, back1, wp1, asked1, fneed1, _}) == S.report(fa, c <> cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) : R.Report}
      DS.rep_lines(dfs, fa, c <> cs, cs, O, N, o, md, src, pd, eof, src1, pd1, eof1, back, wp, asked, back1, wp1, asked1, fneed, fneed1,
        Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(S.StP{o, md, src1, pd1, eof1, back1, wp1, asked1, fneed1, dfs}, cs), S.intext(S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}, c <> cs),
          %Equal.sym(B.Defs, dfs1, dfs, hdf) : {S.intext(S.StP{o, md, src1, pd1, eof1, back1, wp1, asked1, fneed1, _}, cs) == S.intext(S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}, c <> cs) : String}; hi), hrc)



def fed_go2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p0: S.StP, +p1: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p0) == T : R.Report},
  +hg: {S.guard(O, N, p0) == True{} : Bool},
  +hw: {S.WF(fa, p1) == True{} : Bool},
  +hmd: {S.StP.md(p1) == S.StP.md(p0) : S.MdP},
  +ho: {S.StP.o(p1) == S.StP.o(p0) : B.Opts},
  +ha: {S.StP.asked(p1) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +he: {S.StP.eof(p1) == False{} : Bool},
  +hdf: {S.StP.dfs(p1) == S.StP.dfs(p0) : B.Defs},
  +hrc: {S.recs(S.StP.src(p1)) == S.recs(S.StP.src(p0)) : List<&2, P.SrcP>},
  hi: @cs2: List<&2, String> -> {S.intext(p1, cs2) == S.intext(p0, c <> cs2) : String}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(S.mkSt(fa, p1))):
  %he : DO.StepG2(fa, T, cs, O, N, _, Norm.go(S.mkSt(fa, p1)))
  DS.go_ok2(fa, T, cs, O, N, p1, hb, hw,
    Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p0), T, rep_of(fa, cs, O, N, c, p0, p1, hmd, ho, hi(cs), hdf, hrc), hr),
    ha,
    AB.subst(S.MdP, m => {Bool.or(R.RunSt.inbody(S.smd(m)), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}, S.StP.md(p0), S.StP.md(p1),
      Equal.sym(S.MdP, S.StP.md(p1), S.StP.md(p0), hmd), hg))

# The fed state, then go: the step's guarantee.
def fed_go(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p0: S.StP, -X: Norm.St,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p0) == T : R.Report},
  +hg: {S.guard(O, N, p0) == True{} : Bool},
  f: F.Fed(fa, c, p0, X)) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(X)):
  (+p1, f1) = f
  (+e, f2) = f1
  (+hw, f3) = f2
  (+hmd, f4) = f3
  (+ho, f5) = f4
  (+ha, f6) = f5
  (+he, f7) = f6
  (+hdf, f8) = f7
  (+hrc, hi) = f8
  %Equal.sym(Norm.St, X, S.mkSt(fa, p1), e) : DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(_))
  fed_go2(fa, T, c, cs, O, N, p0, p1, hb, hr, hg, hw, hmd, ho, ha, he, hdf, hrc, hi)

# A piece given to a state waiting for more
# =========================================

# After the room.
def pic_core(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))):
  fed_go(fa, T, c, cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs},
    Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs),
    hb, hr, hg, F.core(dfs, fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv))

# The run gets room for the piece (proof_b_drive_chunk.bend's chunk_mb2).
def pic_mb2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +e: {NR.reserve(P.mkRun(rp), len) == P.mkRun(rp2) : NR.Run},
  +hi2: {RN.RunInv(rp2) == True{} : Bool},
  +hs: {P.specRun(rp2) == P.specRun(rp) : R.RunSt}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))):
  +md = {S.MBP{rp} : S.MdP}
  +md2 = {S.MBP{rp2} : S.MdP}
  +hw2 = DO.x9_mk(S.md_ok(md2), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md2, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hi2,
    DO.x9_1(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_4(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw),
    DO.x9_5(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw))
  +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +q2 = {S.StP{o, md2, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +hr2 = Equal.trans(R.Report, S.report(fa, c <> cs, O, N, q2), S.report(fa, c <> cs, O, N, q), T,
    Equal.cong(R.RunSt, R.Report, z => DO.RPX(fa, O, N, o, dfs, z, B.Text.lines(S.intext(q, c <> cs)), S.recs(Nil{})), P.specRun(rp2), P.specRun(rp), hs), hr)
  +hg2 = AB.subst(R.RunSt, z => {Bool.or(R.RunSt.inbody(z), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}, P.specRun(rp), P.specRun(rp2),
    Equal.sym(R.RunSt, P.specRun(rp2), P.specRun(rp), hs), hg)
  %Equal.sym(NR.Run, NR.reserve(P.mkRun(rp), len), P.mkRun(rp2), e) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)))
  pic_core(dfs, fa, T, c, cs, O, N, o, md2, pd, back, wp, fneed, len, t, d, hb, hw2, hr2, hg2, hok, hv)



def pic_mb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  r: &p2: P.RunP -> ({NR.reserve(P.mkRun(rp), len) == P.mkRun(p2) : NR.Run}
    & ({RN.RunInv(p2) == True{} : Bool}
    & ({P.specRun(p2) == P.specRun(rp) : R.RunSt}
    & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32})))) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))):
  (+rp2, r1) = r
  (+e, r2) = r1
  (+hi2, r3) = r2
  (hs, ho) = r3
  pic_mb2(dfs, fa, T, c, cs, O, N, o, rp, rp2, pd, back, wp, fneed, len, t, d, hb, hw, hr, hg, hok, hv, e, hi2, hs)

# By the run's mode (the String mode's run has no buffer).
def pic_md(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Pr.Chunk{C.BT(len, t)})):
  match md:
    case S.MBP{+rp}:
      pic_mb(dfs, fa, T, c, cs, O, N, o, rp, pd, back, wp, fneed, len, t, d, hb, hw, hr, hg, hok, hv,
        RN.run_reserve(rp, len, DO.x8_a(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw)))
    case S.MSP{+s, +qs, +ql, +code}:
      pic_core(dfs, fa, T, c, cs, O, N, o, S.MSP{s, qs, ql, code}, pd, back, wp, fneed, len, t, d, hb, hw, hr, hg, hok, hv)



# step_chunk_pic: by the state (a state waiting for more has no source, is
# before the end of the file and asked nothing).
def step_chunk_pic_h(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)})):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      pic_md(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, len, t, d, hb, DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm), hr, hg, hok, hv)

# W.feed_line
# ===========

# Q.feed without md.reserve: the fed state itself.
def feed_line_h(+fa: List<&2, B.Contig>, +c: String, +p: S.StP, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  F.Fed(fa, c, p, W.feed_line(S.mkSt(fa, p), C.BT(len, t))):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(F.Fed(fa, c, q, W.feed_line(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(F.Fed(fa, c, q, W.feed_line(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd(F.Fed(fa, c, q, W.feed_line(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      F.core(dfs, fa, c, len, t, d, o, md, pd, back, wp, fneed, DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm), hok, hv)

# set_win
# =======

# Nothing was asked: the window stays.
def sw_nil(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +ha: {asked == None{} : Maybe<&2, List<&2, Pr.Req>>}) ->
  {Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), M.truths(fa, Nil{})) == S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs}) : Norm.St}:
  %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, None{}, ha) :
    {Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, _, fneed, dfs}), M.truths(fa, Nil{})) == S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs}) : Norm.St}
  {==}

# The reads of one window were asked: the window of their truthful answers.
def sw_eq2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +ha: {asked == Some{Con{Pr.Req{c, a, b}, t}} : Maybe<&2, List<&2, Pr.Req>>},
  +hp: {Con{Pr.Req{c, a, b}, t} == Norm.parts(c, a, Norm.last_b(t, b)) : List<&2, Pr.Req>},
  wt: {Norm.win_of(Norm.parts(c, a, Norm.last_b(t, b)), M.truths(fa, Norm.parts(c, a, Norm.last_b(t, b)))) == PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) : Norm.Win}
    & {PC.wp_ok(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool}) ->
  {Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), M.truths(fa, Con{Pr.Req{c, a, b}, t})) == S.mkSt(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, Norm.last_b(t, b)), None{}, fneed, dfs}) : Norm.St}:
  (wt1, wt2) = wt
  +bb = Norm.last_b(t, b)
  +rs1 = {Con{Pr.Req{c, a, b}, t} : List<&2, Pr.Req>}
  %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, Some{rs1}, ha) :
    {Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, _, fneed, dfs}), M.truths(fa, rs1)) == S.mkSt(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, bb), None{}, fneed, dfs}) : Norm.St}
  %Equal.sym(List<&2, Pr.Req>, rs1, Norm.parts(c, a, bb), hp) :
    {Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.win_of(_, M.truths(fa, _)), None{}, fneed, dfs} == S.mkSt(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, bb), None{}, fneed, dfs}) : Norm.St}
  Equal.cong(Norm.Win, Norm.St, w => Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, w, None{}, fneed, dfs},
    Norm.win_of(Norm.parts(c, a, bb), M.truths(fa, Norm.parts(c, a, bb))), PC.mkWin(fa, PC.wpOf(fa, c, a, bb)), wt1)

# That window keeps the state good (step_ref_h2's ref_win).
def sw_wf2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool},
  +hmr: {S.mb_reqs(md, Con{Pr.Req{c, a, b}, t}) == True{} : Bool},
  wt: {Norm.win_of(Norm.parts(c, a, Norm.last_b(t, b)), M.truths(fa, Norm.parts(c, a, Norm.last_b(t, b)))) == PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) : Norm.Win}
    & {PC.wp_ok(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool}) ->
  {S.WF(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, Norm.last_b(t, b)), None{}, fneed, dfs}) == True{} : Bool}:
  (wt1, wt2) = wt
  +bb = Norm.last_b(t, b)
  DO.x9_mk(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
    Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, PC.wpOf(fa, c, a, bb)), S.mb_win(md, PC.wpOf(fa, c, a, bb)), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)),
    DO.x8_a(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)), hw),
    DO.x9_1(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)), hw),
    DO.x9_2(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)), hw),
    DO.x9_3(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)), hw),
    DO.x9_4(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)), hw),
    DO.x9_5(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)), hw), wt2, DS.mbw_of(md, fa, c, a, b, t, bb, hmr), DO.x9_8(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src)), hw))



def sw_eq(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +ha: {asked == Some{Con{Pr.Req{c, a, b}, t}} : Maybe<&2, List<&2, Pr.Req>>},
  +hp: {Con{Pr.Req{c, a, b}, t} == Norm.parts(c, a, Norm.last_b(t, b)) : List<&2, Pr.Req>}) ->
  {Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), M.truths(fa, Con{Pr.Req{c, a, b}, t})) == S.mkSt(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, Norm.last_b(t, b)), None{}, fneed, dfs}) : Norm.St}:
  sw_eq2(dfs, fa, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, ha, hp, PCA.win_truths(fa, c, a, Norm.last_b(t, b), hb))

def sw_wf(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool},
  +hmr: {S.mb_reqs(md, Con{Pr.Req{c, a, b}, t}) == True{} : Bool}) ->
  {S.WF(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, Norm.last_b(t, b)), None{}, fneed, dfs}) == True{} : Bool}:
  sw_wf2(dfs, fa, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, hw, hmr, PCA.win_truths(fa, c, a, Norm.last_b(t, b), hb))
