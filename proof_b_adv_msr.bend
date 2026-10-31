import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_frame.bend as FR
import ./proof_b_adv_ms.bend as MS
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_sp.bend as HX
import ./proof_b_adv_injr.bend as IR
import ./proof_b_adv_msx.bend as MSX
import ./proof_s_one.bend as OI
import ./norm_fast.bend as NF
import ./proof_b_lines.bend as LN
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_part.bend as DPT
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_str.bend as T
import ./proof_b_cut_str.bend as CS
import ./proof_b_lines_str.bend as LSS
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A record of a split line in the String mode (norm_seq.bend's ms.line with
# LsR): from an SR source, or read from a record buffer (SP). The machine
# handles it as a body line from the run unticked (its line was counted when
# it was split); the model steps it with rstep. A record has one ALT, so -m
# leaves it whole. Every variable is reusable.

# Bytes
# =====

def bytes_l(+a: String, +b: String, +h: {E.is_bytes(String.append(a, b)) == True{} : Bool}) -> {E.is_bytes(a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      W.and_tt(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(r), W.and_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(r, b)), h),
        bytes_l(r, b, W.and_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(r, b)), h)))

def bytes_r(+a: String, +b: String, +h: {E.is_bytes(String.append(a, b)) == True{} : Bool}) -> {E.is_bytes(b) == True{} : Bool}:
  match a:
    case SNil{}:
      h
    case SCon{+c, +r}:
      bytes_r(r, b, W.and_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(r, b)), h))

# The run's texts stay bytes after any line of bytes.
def stl.k(+dfs: B.Defs, +x: Bool, +i: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +fa: List<&2, B.Contig>, +o: B.Opts, +l: B.Line,
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hsb: {P.st_bytes(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}) == True{} : Bool},
  +hbd: {E.is_bytes(B.Line.body(l)) == True{} : Bool},
  +htm: {E.is_bytes(B.Line.term(l)) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool}) ->
  {P.st_bytes(L.line_step(fa, dfs, o, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, l)) == True{} : Bool}:
  match x i:
    case True{} _:
      hsb
    case False{} False{}:
      MSX.hd_b.k(R.is_chrom_line(B.Line.body(l)), l, 1n+n, False{}, h, c, e, la, b, k, out, ns, False{}, o, hsb, hob, hbd, htm, hlt)
    case False{} True{}:
      +BD = B.Line.body(l)
      +S1 = R.tick(R.RunSt{n, True{}, h, c, e, la, b, k, out, ns, False{}})
      MSX.bi_b(B.Rec.parts(dfs, o, BD), dfs, fa, o, S1, l, B.At{R.RunSt.n(S1), B.Rec.field(B.Rec.fields(BD), 0n), B.Rec.field(B.Rec.fields(BD), 1n)}, B.Rec.pos(B.Rec.fields(BD)), {==},
        hsb, hbd, hlt, htm, hfb)

law stl:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +s: R.RunSt
  for +l: B.Line
  for +hfb: {CD.fa_bytes(fa) == True{} : Bool}
  for +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool}
  for +hsb: {P.st_bytes(s) == True{} : Bool}
  for +hbd: {E.is_bytes(B.Line.body(l)) == True{} : Bool}
  for +htm: {E.is_bytes(B.Line.term(l)) == True{} : Bool}
  for +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool}
  {P.st_bytes(L.line_step(fa, dfs, o, s, l)) == True{} : Bool}

def stl(dfs, fa, o, s, l, hfb, hob, hsb, hbd, htm, hlt):
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      stl.k(dfs, x, i, n, h, c, e, la, b, k, out, ns, fa, o, l, hfb, hob, hsb, hbd, htm, hlt)

# The run unticked
# ================

def ut_pw(+O: String, +N: List<&2, B.Note>, +s: R.RunSt, +x: String) ->
  {Norm.rs_untick(S.pre(O, N, S.with_out(s, x))) == S.pre(O, N, S.with_out(Norm.rs_untick(s), x)) : R.RunSt}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      {==}

def halt_pw(+O: String, +N: List<&2, B.Note>, +s: R.RunSt, +x: String) -> {R.RunSt.halt(S.pre(O, N, S.with_out(s, x))) == R.RunSt.halt(s) : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      {==}

def out_ut(+s: R.RunSt) -> {P.RunSt.out(Norm.rs_untick(s)) == P.RunSt.out(s) : String}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      {==}

def ib_ut(+s: R.RunSt) -> {R.RunSt.inbody(Norm.rs_untick(s)) == R.RunSt.inbody(s) : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      {==}

def halt_ut(+s: R.RunSt) -> {R.RunSt.halt(Norm.rs_untick(s)) == R.RunSt.halt(s) : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      {==}

def sb_ut(+s: R.RunSt, +h: {P.st_bytes(s) == True{} : Bool}) -> {P.st_bytes(Norm.rs_untick(s)) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +hh, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      h

def tu.k(n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +xh: Bool,
  +hn: {Nat.is_le(1n, n) == True{} : Bool}) ->
  {R.tick(Norm.rs_untick(R.RunSt{n, i, h, c, e, la, b, k, o, ns, xh})) == R.RunSt{n, i, h, c, e, la, b, k, o, ns, xh} : R.RunSt}:
  match n:
    case 0n:
      Empty.absurd({R.tick(Norm.rs_untick(R.RunSt{0n, i, h, c, e, la, b, k, o, ns, xh})) == R.RunSt{0n, i, h, c, e, la, b, k, o, ns, xh} : R.RunSt}, W.ft(hn))
    case 1n+m:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, N.sub_zero(m)) : {R.RunSt{1n+_, i, h, c, e, la, b, k, o, ns, xh} == R.RunSt{1n+m, i, h, c, e, la, b, k, o, ns, xh} : R.RunSt}
      {==}

# A run that has counted a line, unticked and ticked again, is as it was.
def tick_untick(+s: R.RunSt, +hn: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool}) -> {R.tick(Norm.rs_untick(s)) == s : R.RunSt}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      tu.k(n, i, h, c, e, la, b, k, o, ns, xh, hn)

# The record step, from the state the driver's run stands for.
law rstep_eq:
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +O: String
  for +N: List<&2, B.Note>
  for +s: R.RunSt
  for +x: String
  for +l: B.Line
  for +hx: {R.RunSt.halt(s) == False{} : Bool}
  for +hib: {R.RunSt.inbody(s) == True{} : Bool}
  for +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool}
  {S.rstep(fa, dfs, o, S.pre(O, N, S.with_out(s, x)), l) == S.pre(O, N, S.pre(x, Nil{}, L.line_step(fa, dfs, o, Norm.rs_untick(s), l))) : R.RunSt}

def rstep_eq(fa, dfs, o, O, N, s, x, l, hx, hib, hout):
  +s0 = Norm.rs_untick(s)
  +X = S.pre(O, N, S.with_out(s, x))
  +ib0 = Equal.trans(Bool, R.RunSt.inbody(s0), R.RunSt.inbody(s), True{}, ib_ut(s), hib)
  +ho0 = {(%Equal.sym(String, P.RunSt.out(Norm.rs_untick(s)), P.RunSt.out(s), out_ut(s)) : {String.is_empty(_) == True{} : Bool}; hout) : {String.is_empty(P.RunSt.out(s0)) == True{} : Bool}}
  %Equal.sym(Bool, R.RunSt.halt(X), False{}, Equal.trans(Bool, R.RunSt.halt(X), R.RunSt.halt(s), False{}, halt_pw(O, N, s, x), hx)) :
    {S.rstep.if(_, fa, dfs, o, X, l) == S.pre(O, N, S.pre(x, Nil{}, L.line_step(fa, dfs, o, s0, l))) : R.RunSt}
  %Equal.sym(R.RunSt, Norm.rs_untick(X), S.pre(O, N, S.with_out(s0, x)), ut_pw(O, N, s, x)) :
    {L.line_step(fa, dfs, o, _, l) == S.pre(O, N, S.pre(x, Nil{}, L.line_step(fa, dfs, o, s0, l))) : R.RunSt}
  %Equal.sym(R.RunSt, S.with_out(s0, x), S.pre(x, Nil{}, s0), MSX.wo_pre(s0, x, ho0)) :
    {L.line_step(fa, dfs, o, S.pre(O, N, _), l) == S.pre(O, N, S.pre(x, Nil{}, L.line_step(fa, dfs, o, s0, l))) : R.RunSt}
  +hg1 = W.or_l(R.RunSt.inbody(S.pre(x, Nil{}, s0)), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)),
    Equal.trans(Bool, R.RunSt.inbody(S.pre(x, Nil{}, s0)), R.RunSt.inbody(s0), True{}, MSX.ib_pre(x, Nil{}, s0), ib0))
  +hg2 = W.or_l(R.RunSt.inbody(s0), Bool.and(String.is_empty(x), List.is_empty(&2, B.Note, Nil{})), ib0)
  %Equal.sym(R.RunSt, L.line_step(fa, dfs, o, S.pre(O, N, S.pre(x, Nil{}, s0)), l), S.pre(O, N, L.line_step(fa, dfs, o, S.pre(x, Nil{}, s0), l)), FR.step_pre(dfs, fa, o, O, N, S.pre(x, Nil{}, s0), l, hg1)) :
    {_ == S.pre(O, N, S.pre(x, Nil{}, L.line_step(fa, dfs, o, s0, l))) : R.RunSt}
  %Equal.sym(R.RunSt, L.line_step(fa, dfs, o, S.pre(x, Nil{}, s0), l), S.pre(x, Nil{}, L.line_step(fa, dfs, o, s0, l)), FR.step_pre(dfs, fa, o, x, Nil{}, s0, l, hg2)) :
    {S.pre(O, N, _) == S.pre(O, N, S.pre(x, Nil{}, L.line_step(fa, dfs, o, s0, l))) : R.RunSt}
  {==}

# Less work: the same measure, fewer records.
def less_mr(+p2: S.StP, +p: S.StP, +he: {S.measure(p2) == S.measure(p) : Nat},
  +hmr: {Nat.is_lt(S.mrec(S.StP.src(p2)), S.mrec(S.StP.src(p))) == True{} : Bool}) -> {S.less(p2, p) == True{} : Bool}:
  %Equal.sym(Nat, S.measure(p2), S.measure(p), he) :
    {Bool.or(Nat.is_lt(_, S.measure(p)), Bool.and(Nat.is_eq(_, S.measure(p)), Nat.is_lt(S.mrec(S.StP.src(p2)), S.mrec(S.StP.src(p))))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(S.measure(p), S.measure(p)), False{}, N.lt_irrefl(S.measure(p))) :
    {Bool.or(_, Bool.and(Nat.is_eq(S.measure(p), S.measure(p)), Nat.is_lt(S.mrec(S.StP.src(p2)), S.mrec(S.StP.src(p))))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(S.measure(p), S.measure(p)), True{}, N.eq_refl(S.measure(p))) :
    {Bool.or(False{}, Bool.and(_, Nat.is_lt(S.mrec(S.StP.src(p2)), S.mrec(S.StP.src(p))))) == True{} : Bool}
  hmr

# After a record the run is in the body and has counted a line.
def rr_s2(+s2: R.RunSt, +qs: List<&2, String>, +ql: Nat, +hib: {R.RunSt.inbody(s2) == True{} : Bool}, +hn: {Nat.is_le(1n, R.RunSt.n(s2)) == True{} : Bool}) ->
  {Bool.and(R.RunSt.inbody(S.smd(MS.msO(s2, qs, ql))), Nat.is_le(1n, R.RunSt.n(S.smd(MS.msO(s2, qs, ql))))) == True{} : Bool}:
  match s2:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +x}:
      %Equal.sym(Bool, i, True{}, hib) : {Bool.and(_, Nat.is_le(1n, n)) == True{} : Bool}
      hn

def lb_body(+l: B.Line, +h: {E.is_bytes(B.Line.text(l)) == True{} : Bool}) -> {E.is_bytes(B.Line.body(l)) == True{} : Bool}:
  match l:
    case B.Line{+b, +t}:
      bytes_l(b, t, h)

def lb_term(+l: B.Line, +h: {E.is_bytes(B.Line.text(l)) == True{} : Bool}) -> {E.is_bytes(B.Line.term(l)) == True{} : Bool}:
  match l:
    case B.Line{+b, +t}:
      bytes_r(b, t, h)

# The String mode reads a record as a body line (the run is in the body).
def mrl_eq(+o: B.Opts, +st: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line, +back: Nat, cx: Norm.Cx, win: Norm.Win,
  +hib: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Norm.ms.line(o, st, qs, ql, Norm.LsR{l}, back, cx, win) == Norm.ms.split(R.Opts.split(o), o, st, qs, ql, Norm.LsR{l}, l, back, cx, win) : Norm.Adv}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      %Equal.sym(Bool, i, True{}, hib) : {Norm.ms.line.k(_, o, R.RunSt{n, _, h, c, e, la, b, k, out, ns, x}, qs, ql, Norm.LsR{l}, l, back, cx, win) == Norm.ms.split(R.Opts.split(o), o, R.RunSt{n, _, h, c, e, la, b, k, out, ns, x}, qs, ql, Norm.LsR{l}, l, back, cx, win) : Norm.Adv}
      {==}

# The record handled (VRes, VSame): the next state, without it, stands for T.
def rec_went(+dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  hRG: @X: R.RunSt -> {S.RG(S.recs(src), fa, dfs, o, X) == S.RG(S.recs(src2), fa, dfs, o, S.rstep(fa, dfs, o, X, l)) : R.RunSt},
  +hbl: MSX.BLM(fa, dfs, o, Norm.rs_untick(s), l, r),
  +hpl: {S.plain(src) == S.plain(src2) : List<&2, P.SrcP>},
  +hms: {S.msrc(src2) == S.msrc(src) : Nat},
  +hmr: {Nat.is_lt(S.mrec(src2), S.mrec(src)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  +hone: {Nat.is_lt(L.n_alts(B.Line.body(l)), 2n) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(MSX.X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(MSX.X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.done(o, R.body_line(r, R.tick(Norm.rs_untick(s)), o, l, Norm.at_of(R.RunSt.n(R.tick(Norm.rs_untick(s))), J.pfs(B.Line.body(l))), B.Rec.pos(J.pfs(B.Line.body(l)))), qs, ql, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp))):
  +s0 = Norm.rs_untick(s)
  +s2 = R.body_line(r, R.tick(s0), o, l, Norm.at_of(R.RunSt.n(R.tick(s0)), J.pfs(B.Line.body(l))), B.Rec.pos(J.pfs(B.Line.body(l))))
  +ls = L.line_step(fa, dfs, o, s0, l)
  +p = MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)
  +p2 = MSX.SM2(dfs, o, s2, qs, ql, src2, pd, eof, wp)
  +pb = MSX.SO(dfs, o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})
  +hx0 = Equal.trans(Bool, R.RunSt.halt(s0), R.RunSt.halt(s), False{}, halt_ut(s), hx)
  +hib0 = Equal.trans(Bool, R.RunSt.inbody(s0), R.RunSt.inbody(s), True{}, ib_ut(s), hib)
  +hib2 = MSX.ib2(dfs, fa, o, s0, l, s2, hbl, hib0)
  +hn2 = {(%Equal.sym(R.RunSt, s2, ls, hbl) : {Nat.is_le(1n, R.RunSt.n(_)) == True{} : Bool}; %Equal.sym(Nat, R.RunSt.n(ls), 1n+R.RunSt.n(s0), HX.n_ls(fa, dfs, o, s0, l, hx0, hib0)) : {Nat.is_le(1n, _) == True{} : Bool}; N.le_zero_l(R.RunSt.n(s0))) :
    {Nat.is_le(1n, R.RunSt.n(s2)) == True{} : Bool}}
  +hsb2 = {(%Equal.sym(R.RunSt, s2, ls, hbl) : {P.st_bytes(_) == True{} : Bool}; stl(dfs, fa, o, s0, l, hfb, hob, sb_ut(s, hsb), lb_body(l, hlt), lb_term(l, hlt), hlt)) : {P.st_bytes(s2) == True{} : Bool}}
  +hmd = MSX.mdok_msO(s2, qs, ql, hql, hxb, hsb2,
    W.or_l(R.RunSt.inbody(s2), String.is_empty(String.append(MSX.X0(qs), P.RunSt.out(s2))), hib2),
    W.or_l(R.RunSt.inbody(s2), List.is_empty(&2, B.Note, P.RunSt.notes(s2)), hib2))
  +hc2 = MSX.wfC(fa, pb, hw2)
  +b0 = W.W0(fa, pb)
  +b1 = W.W1(fa, pb)
  +b2 = W.W2(fa, pb)
  +b3 = W.W3(fa, pb)
  +b4 = W.W4(fa, pb)
  +b5 = W.W5(fa, pb)
  +b6 = W.W6(fa, pb)
  +b7 = W.W7(fa, pb)
  +b8 = W.W8(fa, pb)
  +AB = E.all_bytes(S.opts_args(o))
  +h8l = W.and_l(Bool.and(AB, S.recs_first(src2)), S.recs_run(S.MSP{s, qs, ql, None{}}, src2), W.c9_8(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2))
  +b8n = W.and_tt(Bool.and(AB, S.recs_first(src2)), S.recs_run(MS.msO(s2, qs, ql), src2), h8l,
    IR.or_tr(List.is_empty(&2, P.SrcP, S.recs(src2)), Bool.and(R.RunSt.inbody(S.smd(MS.msO(s2, qs, ql))), Nat.is_le(1n, R.RunSt.n(S.smd(MS.msO(s2, qs, ql))))), rr_s2(s2, qs, ql, hib2, hn2)))
  +hwf = Equal.trans(Bool, S.WF(fa, p2), W.C9(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2)), True{}, W.wf_c9(fa, p2),
    W.c9_mk(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2),
      hmd, W.c9_1(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2), W.c9_2(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2), W.c9_3(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2),
      W.c9_4(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2), W.c9_5(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2), W.c9_6(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2), MS.mbw_msO(s2, qs, ql, wp), b8n))
  +X = S.pre(O, N, S.with_out(s, MSX.X0(qs)))
  +R0 = String.append(P.pdtext(pd), S.concat_if(eof, cs))
  +hrp = {(%MSX.defs_body(dfs, cs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hib) : {R.finish(L.run.go(B.Text.lines(MS.ITX(src, pd, eof, cs)), fa, _, o, S.RG(S.recs(src), fa, _, o, X))) == T : R.Report}; hr) :
    {R.finish(L.run.go(B.Text.lines(MS.ITX(src, pd, eof, cs)), fa, dfs, o, S.RG(S.recs(src), fa, dfs, o, X))) == T : R.Report}}
  +hrep = {(%MS.rep_msO(dfs, fa, cs, O, N, o, s2, qs, ql, src2, pd, eof, 0n, wp, None{}, False{}) : {_ == T : R.Report};
      %Equal.sym(B.Defs, S.DEFS(p2, cs), dfs, MSX.defs_body2(dfs, cs, o, s2, qs, ql, src2, pd, eof, wp, hib2)) :
        {R.finish(L.run.go(B.Text.lines(S.intext(p2, cs)), fa, _, o, S.RG(S.recs(src2), fa, _, o, S.pre(O, N, S.smd(MS.msO(s2, qs, ql)))))) == T : R.Report};
      %Equal.sym(R.RunSt, S.smd(MS.msO(s2, qs, ql)), S.pre(MSX.X0(qs), Nil{}, s2), MSX.smd_pre(s2, qs, ql)) :
        {R.finish(L.run.go(B.Text.lines(S.intext(p2, cs)), fa, dfs, o, S.RG(S.recs(src2), fa, dfs, o, S.pre(O, N, _)))) == T : R.Report};
      %Equal.sym(R.RunSt, s2, ls, hbl) :
        {R.finish(L.run.go(B.Text.lines(S.intext(p2, cs)), fa, dfs, o, S.RG(S.recs(src2), fa, dfs, o, S.pre(O, N, S.pre(MSX.X0(qs), Nil{}, _))))) == T : R.Report};
      %rstep_eq(fa, dfs, o, O, N, s, MSX.X0(qs), l, hx, hib, hout) :
        {R.finish(L.run.go(B.Text.lines(S.intext(p2, cs)), fa, dfs, o, S.RG(S.recs(src2), fa, dfs, o, _))) == T : R.Report};
      %hRG(X) : {R.finish(L.run.go(B.Text.lines(S.intext(p2, cs)), fa, dfs, o, _)) == T : R.Report};
      %hpl : {R.finish(L.run.go(B.Text.lines(String.append(P.srcstext(_), R0)), fa, dfs, o, S.RG(S.recs(src), fa, dfs, o, X))) == T : R.Report};
      hrp) : {S.report(fa, cs, O, N, p2) == T : R.Report}}
  (p2, (MSX.est_went(dfs, fa, o, s2, qs, ql, src2, pd, eof, wp), (hwf, (hrep, (less_mr(p2, p, Equal.trans(Nat, S.measure(p2), S.msrc(src2), S.msrc(src), Equal.sym(Nat, S.msrc(src2), S.measure(p2), MS.meas_msO(dfs, o, s2, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})), hms), hmr),
    ({==}, ({==}, (MSX.guard_went(dfs, O, N, o, s2, qs, ql, src2, pd, eof, wp, W.or_l(R.RunSt.inbody(s2), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), hib2)), ({==}, (Equal.trans(B.Defs, S.DEFS(p2, cs), dfs, S.DEFS(MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), cs), MSX.defs_body2(dfs, cs, o, s2, qs, ql, src2, pd, eof, wp, hib2), Equal.sym(B.Defs, S.DEFS(MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), cs), dfs, MSX.defs_body(dfs, cs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hib))), Unit{}))))))))))

# The record put back for reads (VWant): as an SR source, the run as it was.
def rec_want(+dfs: B.Defs, +reqs: List<&2, Pr.Req>, +bk: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  hRG: @X: R.RunSt -> {S.RG(S.recs(src), fa, dfs, o, X) == S.RG(S.recs(src2), fa, dfs, o, S.rstep(fa, dfs, o, X, l)) : R.RunSt},
  hok: MSX.RQOK(reqs),
  +hpl: {S.plain(src) == S.plain(src2) : List<&2, P.SrcP>},
  +hms: {S.msrc(src2) == S.msrc(src) : Nat},
  +hmr: {Nat.is_lt(S.mrec(src2), S.mrec(src)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  +hone: {Nat.is_lt(L.n_alts(B.Line.body(l)), 2n) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(MSX.X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(MSX.X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.Want{Norm.St{o, Norm.MS{R.tick(Norm.rs_untick(s)), qs, ql, None{}}, Con{Norm.SR{l}, P.mkSrcs(src2)}, P.mkPd(pd), eof, bk, CD.mkWin(fa, wp), Some{reqs}, False{}, dfs}, reqs}):
  (h1, h23) = hok
  (h2, h3) = h23
  +p3 = MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, bk, wp, Some{reqs}, False{})
  +X = S.pre(O, N, S.with_out(s, MSX.X0(qs)))
  +R0 = String.append(P.pdtext(pd), S.concat_if(eof, cs))
  +hrp = {(%MSX.defs_body(dfs, cs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hib) : {R.finish(L.run.go(B.Text.lines(MS.ITX(src, pd, eof, cs)), fa, _, o, S.RG(S.recs(src), fa, _, o, X))) == T : R.Report}; hr) :
    {R.finish(L.run.go(B.Text.lines(MS.ITX(src, pd, eof, cs)), fa, dfs, o, S.RG(S.recs(src), fa, dfs, o, X))) == T : R.Report}}
  +hrep = {(%Equal.sym(B.Defs, S.DEFS(p3, cs), dfs, MSX.defs_body(dfs, cs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, bk, wp, Some{reqs}, False{}, hib)) :
        {R.finish(L.run.go(B.Text.lines(S.intext(p3, cs)), fa, _, o, S.RG(S.recs(Con{P.SRP{l}, src2}), fa, _, o, X))) == T : R.Report};
      %hRG(X) : {R.finish(L.run.go(B.Text.lines(S.intext(p3, cs)), fa, dfs, o, _)) == T : R.Report};
      %hpl : {R.finish(L.run.go(B.Text.lines(String.append(P.srcstext(_), R0)), fa, dfs, o, S.RG(S.recs(src), fa, dfs, o, X))) == T : R.Report};
      hrp) : {S.report(fa, cs, O, N, p3) == T : R.Report}}
  %Equal.sym(R.RunSt, R.tick(Norm.rs_untick(s)), s, tick_untick(s, hn1)) :
    S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.Want{Norm.St{o, Norm.MS{_, qs, ql, None{}}, Con{Norm.SR{l}, P.mkSrcs(src2)}, P.mkPd(pd), eof, bk, CD.mkWin(fa, wp), Some{reqs}, False{}, dfs}, reqs})
  (p3, ({==}, (hw3,
    (hrep, (h1, (h2, (MSX.asked_some(reqs, h3), (MSX.stop_f(s, qs, ql, hx), ({==}, ({==}, (hg, ({==}, (Equal.trans(B.Defs, S.DEFS(p3, cs), dfs, S.DEFS(MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), cs), MSX.defs_body(dfs, cs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, bk, wp, Some{reqs}, False{}, hib), Equal.sym(B.Defs, S.DEFS(MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), cs), dfs, MSX.defs_body(dfs, cs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hib))), Unit{})))))))))))))

def rec_v(+dfs: B.Defs, +v: MSX.VdP, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  hRG: @X: R.RunSt -> {S.RG(S.recs(src), fa, dfs, o, X) == S.RG(S.recs(src2), fa, dfs, o, S.rstep(fa, dfs, o, X, l)) : R.RunSt},
  hok: MSX.vdOK(fa, B.Line.body(l), v),
  +hpw: {B.Rec.parts(dfs, o, B.Line.body(l)) == B.Whole{} : B.Parts},
  +hpl: {S.plain(src) == S.plain(src2) : List<&2, P.SrcP>},
  +hms: {S.msrc(src2) == S.msrc(src) : Nat},
  +hmr: {Nat.is_lt(S.mrec(src2), S.mrec(src)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  +hone: {Nat.is_lt(L.n_alts(B.Line.body(l)), 2n) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(MSX.X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(MSX.X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.body(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, l, J.pfs(B.Line.body(l)), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, MSX.mkVd(fa, wp, v))):
  match v:
    case MSX.VRP{+r}:
    +hx0 = Equal.trans(Bool, R.RunSt.halt(Norm.rs_untick(s)), R.RunSt.halt(s), False{}, halt_ut(s), hx)
    +hib0 = Equal.trans(Bool, R.RunSt.inbody(Norm.rs_untick(s)), R.RunSt.inbody(s), True{}, ib_ut(s), hib)
      +hj = {hok : {r == L.judge(fa, B.Line.body(l)) : B.Res}}
      rec_went(dfs, r, fa, T, cs, O, N, o, s, qs, ql, l, src, src2, pd, eof, back, wp, asked, fneed, hRG, MSX.blm_of(fa, dfs, o, Norm.rs_untick(s), l, r, hx0, hib0, MSX.bl_eq(dfs, r, fa, o, Norm.rs_untick(s), l, hj, hpw)), hpl, hms, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hfb, hv)
    case MSX.VSP{}:
    +hx0 = Equal.trans(Bool, R.RunSt.halt(Norm.rs_untick(s)), R.RunSt.halt(s), False{}, halt_ut(s), hx)
    +hib0 = Equal.trans(Bool, R.RunSt.inbody(Norm.rs_untick(s)), R.RunSt.inbody(s), True{}, ib_ut(s), hib)
      +hj = {hok : {B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(l))), B.Line.body(l), False{}} == L.judge(fa, B.Line.body(l)) : B.Res}}
      rec_went(dfs, B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(l))), B.Line.body(l), False{}}, fa, T, cs, O, N, o, s, qs, ql, l, src, src2, pd, eof, back, wp, asked, fneed, hRG, MSX.blm_of(fa, dfs, o, Norm.rs_untick(s), l, B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(l))), B.Line.body(l), False{}}, hx0, hib0, MSX.bl_eq(dfs, B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(l))), B.Line.body(l), False{}}, fa, o, Norm.rs_untick(s), l, hj, hpw)), hpl, hms, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hfb, hv)
    case MSX.VWP{+reqs, +bk}:
      (hq1, hc) = hok
      rec_want(dfs, reqs, bk, fa, T, cs, O, N, o, s, qs, ql, l, src, src2, pd, eof, back, wp, asked, fneed, hRG, hq1, hpl, hms, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hfb, hv)

def rec_vd(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  hRG: @X: R.RunSt -> {S.RG(S.recs(src), fa, dfs, o, X) == S.RG(S.recs(src2), fa, dfs, o, S.rstep(fa, dfs, o, X, l)) : R.RunSt},
  g: MSX.VdG(fa, wp, back, B.Line.body(l)),
  +hpw: {B.Rec.parts(dfs, o, B.Line.body(l)) == B.Whole{} : B.Parts},
  +hpl: {S.plain(src) == S.plain(src2) : List<&2, P.SrcP>},
  +hms: {S.msrc(src2) == S.msrc(src) : Nat},
  +hmr: {Nat.is_lt(S.mrec(src2), S.mrec(src)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  +hone: {Nat.is_lt(L.n_alts(B.Line.body(l)), 2n) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(MSX.X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(MSX.X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.body(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, l, J.pfs(B.Line.body(l)), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, Norm.verdict(back, CD.mkWin(fa, wp), J.pfs(B.Line.body(l)), B.Line.body(l)))):
  (+v, pr) = g
  (heq, hok) = pr
  %Equal.sym(Norm.Vd, Norm.verdict(back, CD.mkWin(fa, wp), J.pfs(B.Line.body(l)), B.Line.body(l)), MSX.mkVd(fa, wp, v), heq) :
    S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.body(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, l, J.pfs(B.Line.body(l)), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, _))
  rec_v(dfs, v, fa, T, cs, O, N, o, s, qs, ql, l, src, src2, pd, eof, back, wp, asked, fneed, hRG, hok, hpw, hpl, hms, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hfb, hv)

def rec_sp(+dfs: B.Defs, sp: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  hRG: @X: R.RunSt -> {S.RG(S.recs(src), fa, dfs, o, X) == S.RG(S.recs(src2), fa, dfs, o, S.rstep(fa, dfs, o, X, l)) : R.RunSt},
  +hsp: {R.Opts.split(o) == sp : Bool},
  +hpl: {S.plain(src) == S.plain(src2) : List<&2, P.SrcP>},
  +hms: {S.msrc(src2) == S.msrc(src) : Nat},
  +hmr: {Nat.is_lt(S.mrec(src2), S.mrec(src)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  +hone: {Nat.is_lt(L.n_alts(B.Line.body(l)), 2n) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(MSX.X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(MSX.X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.split(sp, o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, l, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp))):
  match sp:
    case False{}:
      rec_vd(dfs, fa, T, cs, O, N, o, s, qs, ql, l, src, src2, pd, eof, back, wp, asked, fneed, hRG, MSX.vd_ok(fa, wp, back, B.Line.body(l), hfb, hv), MSX.nosplit_whole(dfs, o, B.Line.body(l), hsp), hpl, hms, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hfb, hv)
    case True{}:
      %Equal.sym(B.Parts, B.Rec.parts(dfs, o, B.Line.body(l)), B.Whole{}, OI.one_parts(dfs, o, B.Line.body(l), hone)) :
        S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.parts.k(_, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, l, back, CD.mkWin(fa, wp)))
      rec_vd(dfs, fa, T, cs, O, N, o, s, qs, ql, l, src, src2, pd, eof, back, wp, asked, fneed, hRG, MSX.vd_ok(fa, wp, back, B.Line.body(l), hfb, hv), OI.one_parts(dfs, o, B.Line.body(l), hone), hpl, hms, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hfb, hv)

# A record in the String mode: the next state, with it handled or put back,
# stands for T.
def rec_line(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  hRG: @X: R.RunSt -> {S.RG(S.recs(src), fa, dfs, o, X) == S.RG(S.recs(src2), fa, dfs, o, S.rstep(fa, dfs, o, X, l)) : R.RunSt},

  +hpl: {S.plain(src) == S.plain(src2) : List<&2, P.SrcP>},
  +hms: {S.msrc(src2) == S.msrc(src) : Nat},
  +hmr: {Nat.is_lt(S.mrec(src2), S.mrec(src)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  +hone: {Nat.is_lt(L.n_alts(B.Line.body(l)), 2n) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(MSX.X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(MSX.X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.line(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp))):
  +hib0 = Equal.trans(Bool, R.RunSt.inbody(Norm.rs_untick(s)), R.RunSt.inbody(s), True{}, ib_ut(s), hib)
  %Equal.sym(Norm.Adv, Norm.ms.line(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp)), Norm.ms.split(R.Opts.split(o), o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, l, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp)), mrl_eq(o, Norm.rs_untick(s), qs, ql, l, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp), hib0)) : S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), _)
  rec_sp(dfs, R.Opts.split(o), fa, T, cs, O, N, o, s, qs, ql, l, src, src2, pd, eof, back, wp, asked, fneed, hRG, {==}, hpl, hms, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hfb, hv)

# Facts of a state's run and sources
# ==================================

def n_wo(+st: R.RunSt, +x: String) -> {R.RunSt.n(S.with_out(st, x)) == R.RunSt.n(st) : Nat}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o, +ns, +xh}:
      {==}

# While records wait, the run is in the body and has counted their line.
def rr_ib(+s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +h: {Bool.and(R.RunSt.inbody(S.smd(S.MSP{s, qs, ql, None{}})), Nat.is_le(1n, R.RunSt.n(S.smd(S.MSP{s, qs, ql, None{}})))) == True{} : Bool}) ->
  {R.RunSt.inbody(s) == True{} : Bool}:
  Equal.trans(Bool, R.RunSt.inbody(s), R.RunSt.inbody(S.with_out(s, MSX.X0(qs))), True{}, Equal.sym(Bool, R.RunSt.inbody(S.with_out(s, MSX.X0(qs))), R.RunSt.inbody(s), MSX.ib_wo(s, MSX.X0(qs))),
    W.and_l(R.RunSt.inbody(S.with_out(s, MSX.X0(qs))), Nat.is_le(1n, R.RunSt.n(S.with_out(s, MSX.X0(qs)))), h))

def rr_n(+s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +h: {Bool.and(R.RunSt.inbody(S.smd(S.MSP{s, qs, ql, None{}})), Nat.is_le(1n, R.RunSt.n(S.smd(S.MSP{s, qs, ql, None{}})))) == True{} : Bool}) ->
  {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool}:
  {(%n_wo(s, MSX.X0(qs)) : {Nat.is_le(1n, _) == True{} : Bool}; W.and_r(R.RunSt.inbody(S.with_out(s, MSX.X0(qs))), Nat.is_le(1n, R.RunSt.n(S.with_out(s, MSX.X0(qs)))), h)) :
    {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool}}

def lf_nl(+x: String) -> {S.ends_lf(String.append(x, "\n")) == True{} : Bool}:
  IR.lf_pre(x, "\n", {==}, {==})

# The state with a record source taken off the front (its record handled).
def wf_tl_rec(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool}) ->
  {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, rest, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool}:
  +pp = MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)
  +p2 = MSX.SO(dfs, o, s, qs, ql, rest, pd, eof, 0n, wp, None{}, False{})
  +hc = MSX.wfC(fa, pp, hw)
  +m0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +E0 = String.is_empty(P.pdtext(pd))
  +MD = {S.MSP{s, qs, ql, None{}} : S.MdP}
  +AB = E.all_bytes(S.opts_args(o))
  +RR0 = Bool.and(R.RunSt.inbody(S.smd(MD)), Nat.is_le(1n, R.RunSt.n(S.smd(MD))))
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +hab = W.and_l(Bool.and(AB, Bool.and(S.one_alt(l), S.recs_first(rest))), RR0, h8)
  Equal.trans(Bool, S.WF(fa, p2), W.C9(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2)), True{}, W.wf_c9(fa, p2),
    W.c9_mk(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2),
      W.c9_0(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), MSX.srcs_tl(P.SRP{l}, rest, W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)), W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.or_r(S.src_empty(rest), E0, W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      MSX.w5_tl(eof, E0, B.Line.text(l), P.srcstext(rest), W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.and_tt(Bool.and(AB, S.recs_first(rest)), S.recs_run(MD, rest),
        W.and_tt(AB, S.recs_first(rest), W.and_l(AB, Bool.and(S.one_alt(l), S.recs_first(rest)), hab), W.and_r(S.one_alt(l), S.recs_first(rest), W.and_r(AB, Bool.and(S.one_alt(l), S.recs_first(rest)), hab))),
        W.or_r(List.is_empty(&2, P.SrcP, S.recs(rest)), RR0, W.and_r(Bool.and(AB, Bool.and(S.one_alt(l), S.recs_first(rest))), RR0, h8)))))

# The state with a record put in front of sources src2 (a source first).
def wf_pre_rec(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line, +sp0: P.SrcP, +r0: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: CD.WP,
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{sp0, r0}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hlb: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hlf: {S.ends_lf(B.Line.text(l)) == True{} : Bool},
  +hone: {S.one_alt(l) == True{} : Bool},
  +hpe: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hrr: {Bool.and(R.RunSt.inbody(S.smd(S.MSP{s, qs, ql, None{}})), Nat.is_le(1n, R.RunSt.n(S.smd(S.MSP{s, qs, ql, None{}})))) == True{} : Bool}) ->
  {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, Con{sp0, r0}}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool}:
  +pb = MSX.SO(dfs, o, s, qs, ql, Con{sp0, r0}, pd, eof, 0n, wp, None{}, False{})
  +p3 = MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, Con{sp0, r0}}, pd, eof, 0n, wp, None{}, False{})
  +hc = MSX.wfC(fa, pb, hw2)
  +b0 = W.W0(fa, pb)
  +b1 = W.W1(fa, pb)
  +b2 = W.W2(fa, pb)
  +b3 = W.W3(fa, pb)
  +b4 = W.W4(fa, pb)
  +b5 = W.W5(fa, pb)
  +b6 = W.W6(fa, pb)
  +b7 = W.W7(fa, pb)
  +b8 = W.W8(fa, pb)
  +AB = E.all_bytes(S.opts_args(o))
  +h8 = W.c9_8(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc)
  +hab = W.and_l(Bool.and(AB, S.recs_first(Con{sp0, r0})), S.recs_run(S.MSP{s, qs, ql, None{}}, Con{sp0, r0}), h8)
  Equal.trans(Bool, S.WF(fa, p3), W.C9(W.W0(fa, p3), W.W1(fa, p3), W.W2(fa, p3), W.W3(fa, p3), W.W4(fa, p3), W.W5(fa, p3), W.W6(fa, p3), W.W7(fa, p3), W.W8(fa, p3)), True{}, W.wf_c9(fa, p3),
    W.c9_mk(W.W0(fa, p3), W.W1(fa, p3), W.W2(fa, p3), W.W3(fa, p3), W.W4(fa, p3), W.W5(fa, p3), W.W6(fa, p3), W.W7(fa, p3), W.W8(fa, p3),
      W.c9_0(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc),
      W.and_tt(Bool.and(E.is_bytes(B.Line.text(l)), S.ends_lf(B.Line.text(l))), S.srcs_ok(Con{sp0, r0}), W.and_tt(E.is_bytes(B.Line.text(l)), S.ends_lf(B.Line.text(l)), hlb, hlf), W.c9_1(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc)),
      W.c9_2(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc), W.c9_3(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc), hpe,
      IR.eof_lf(eof, pd, P.srcstext(Con{sp0, r0}), P.srcstext(Con{P.SRP{l}, Con{sp0, r0}}), hx2 => IR.lf_app(B.Line.text(l), P.srcstext(Con{sp0, r0}), hlf, hx2), W.c9_5(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc)),
      W.c9_6(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc), W.c9_7(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc),
      W.and_tt(Bool.and(AB, Bool.and(S.one_alt(l), S.recs_first(Con{sp0, r0}))), S.recs_run(S.MSP{s, qs, ql, None{}}, Con{P.SRP{l}, Con{sp0, r0}}),
        W.and_tt(AB, Bool.and(S.one_alt(l), S.recs_first(Con{sp0, r0})), W.and_l(AB, S.recs_first(Con{sp0, r0}), hab),
          W.and_tt(S.one_alt(l), S.recs_first(Con{sp0, r0}), hone, W.and_r(AB, S.recs_first(Con{sp0, r0}), hab))),
        hrr)))

def ms_sr.k(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  mf: MSX.MDF(s, qs, ql),
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  +hone: {S.one_alt(l) == True{} : Bool},
  +hlt: {P.src_ok(P.SRP{l}) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp))):
  (hql, m1) = mf
  (hxb, m2) = m1
  (hsb, m3) = m2
  (hout, m4) = m3
  rec_line(dfs, fa, T, cs, O, N, o, s, qs, ql, l, Con{P.SRP{l}, rest}, rest, pd, eof, back, wp, asked, fneed,
    X => {==}, {==}, {==}, MSX.lt2(S.mrec(rest)), hr, hg, hx, hib, hn1, hone, hlt,
    wf_tl_rec(dfs, fa, o, s, qs, ql, l, rest, pd, eof, back, wp, asked, fneed, hw), hw,
    hql, hxb, hsb, hout, hob, hb, hv)

# A record from an SR source in the String mode.
def ms_sr(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp))):
  +pp = MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed)
  +hc = MSX.wfC(fa, pp, hw)
  +m0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +MD = {S.MSP{s, qs, ql, None{}} : S.MdP}
  +AB = E.all_bytes(S.opts_args(o))
  +RR0 = Bool.and(R.RunSt.inbody(S.smd(MD)), Nat.is_le(1n, R.RunSt.n(S.smd(MD))))
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +hab = W.and_l(Bool.and(AB, Bool.and(S.one_alt(l), S.recs_first(rest))), RR0, h8)
  +hrr = W.and_r(Bool.and(AB, Bool.and(S.one_alt(l), S.recs_first(rest))), RR0, h8)
  mf = MSX.md_facts(s, qs, ql, W.c9_0(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc))
  ms_sr.k(dfs, fa, T, cs, O, N, o, s, qs, ql, l, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, mf,
    rr_ib(s, qs, ql, hrr), rr_n(s, qs, ql, hrr), W.and_l(S.one_alt(l), S.recs_first(rest), W.and_r(AB, Bool.and(S.one_alt(l), S.recs_first(rest)), hab)),
    MSX.src_hd(P.SRP{l}, rest, W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)), W.and_l(AB, Bool.and(S.one_alt(l), S.recs_first(rest)), hab), W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc))

# A record buffer in the String mode (norm_seq.bend's sp.s): dropped when
# read to its end; else its next record (ms.sb with hold), as above.
def msr_done(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hle: {U32.is_le(len, at) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), None{}, fneed, dfs}}):
  +pp = MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +hc = MSX.wfC(fa, pp, hw)
  +m0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +MD = {S.MSP{s, qs, ql, None{}} : S.MdP}
  +AB = E.all_bytes(S.opts_args(o))
  +X = P.srctext(P.SPP{len, t, d, at})
  +RF0 = Bool.and(S.rtok(X), S.recs_first(rest))
  +RR0 = Bool.and(R.RunSt.inbody(S.smd(MD)), Nat.is_le(1n, R.RunSt.n(S.smd(MD))))
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +h01 = W.and_l(Bool.and(AB, RF0), RR0, h8)
  +hrr = W.and_r(Bool.and(AB, RF0), RR0, h8)
  +hrt = W.and_l(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, h01))
  +h1 = W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +hso = HX.srcs_head_p(rest, len, t, d, at, h1)
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +EP = String.is_empty(P.pdtext(pd))
  +q = MSX.SO(dfs, o, s, qs, ql, rest, pd, eof, back, wp, None{}, fneed)
  +hX = HX.em_sp(len, t, d, at, hok, hle)
  +w8 = W.and_tt(Bool.and(AB, S.recs_first(rest)), S.recs_run(MD, rest),
    W.and_tt(AB, S.recs_first(rest), W.and_l(AB, RF0, h01), W.and_r(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, h01))),
    W.or_r(List.is_empty(&2, P.SrcP, S.recs(rest)), RR0, hrr))
  +w5 = {(%hX : {Bool.or(Bool.not(eof), Bool.and(EP, S.ends_lf(String.append(_, P.srcstext(rest))))) == True{} : Bool}; W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)) :
    {Bool.or(Bool.not(eof), Bool.and(EP, S.ends_lf(P.srcstext(rest)))) == True{} : Bool}}
  +M = S.measure(pp)
  +MR = S.mrec(rest)
  +x1 = U32.to_nat((len - at : U32))
  (q,
    ({==},
    (W.c9_mk(m0, W.W1(fa, q), a2, a3, W.W4(fa, q), W.W5(fa, q), a6, a7, W.W8(fa, q), W.c9_0(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
        DPT.srcs_tl(rest, P.SPP{len, t, d, at}, h1),
        W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
        W.or_r(S.src_empty(rest), EP, W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
        w5,
        W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), w8),
    ({%hX :
        {R.finish(L.run.go(B.Text.lines(S.intext(pp, cs)), fa, S.DEFS(pp, cs), o, S.RG(S.recs(rest), fa, S.DEFS(pp, cs), o, S.rgo(B.Text.lines(_), fa, S.DEFS(pp, cs), o, S.pre(O, N, S.smd(MD)))))) == T : R.Report};
      hr : {S.report(fa, cs, O, N, q) == T : R.Report}},
    (W.or_r(Nat.is_lt(M, M), Bool.and(Nat.is_eq(M, M), Nat.is_lt(MR, Nat.add(Nat.add(x1, 2n), MR))),
        W.and_tt(Nat.is_eq(M, M), Nat.is_lt(MR, Nat.add(Nat.add(x1, 2n), MR)), N.eq_refl(M), MSX.meas_drop2(x1, MR))),
    ({==}, ({==}, (hg, ({==}, (W.defs_keep(pp, q, cs, {==}, {==}, {==}), Unit{}))))))))))

# The records' count after the next record: lower.
def mrec_sp(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>,
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hat: {U32.is_le(at, len) == True{} : Bool},
  +hinc: {LI.n((j + 1 : U32)) == Nat.add(LI.n(j), 1n) : Nat}) ->
  {Nat.is_lt(S.mrec(Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}), S.mrec(Con{P.SPP{len, t, d, at}, rest})) == True{} : Bool}:
  +M = S.mrec(rest)
  +x1 = LI.n((len - (j + 1 : U32) : U32))
  +x2 = LI.n((len - at : U32))
  +k1 = {%Equal.sym(Nat, x1, Nat.sub(LI.n(len), LI.n((j + 1 : U32))), LP.sub_u(len, (j + 1 : U32), LI.u2n((j + 1 : U32), len, hle))) : {Nat.is_lt(_, x2) == True{} : Bool};
    %Equal.sym(Nat, x2, Nat.sub(LI.n(len), LI.n(at)), LP.sub_u(len, at, LI.u2n(at, len, hat))) : {Nat.is_lt(Nat.sub(LI.n(len), LI.n((j + 1 : U32))), _) == True{} : Bool};
    %Equal.sym(Nat, LI.n((j + 1 : U32)), Nat.add(LI.n(j), 1n), hinc) : {Nat.is_lt(Nat.sub(LI.n(len), _), Nat.sub(LI.n(len), LI.n(at))) == True{} : Bool};
    LI.lt_sub1(LI.n(len), LI.n(at), LI.n(j), hal, hlt) : {Nat.is_lt(x1, x2) == True{} : Bool}}
  N.lt_add_mono_r(M, Nat.add(x1, 2n), Nat.add(x2, 2n), N.lt_add_mono_r(2n, x1, x2, k1))

def msr_rec.k(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +j: U32,
  mf: MSX.MDF(s, qs, ql),
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hn1: {Nat.is_le(1n, R.RunSt.n(s)) == True{} : Bool},
  hRG: @X: R.RunSt -> {S.RG(S.recs(Con{P.SPP{len, t, d, at}, rest}), fa, dfs, o, X) == S.RG(S.recs(Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}), fa, dfs, o, S.rstep(fa, dfs, o, X, Norm.line(P.btext(len, t, at, (j - at : U32))))) : R.RunSt},
  +hmr: {Nat.is_lt(S.mrec(Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}), S.mrec(Con{P.SPP{len, t, d, at}, rest})) == True{} : Bool},
  +hone: {Nat.is_lt(L.n_alts(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), 2n) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32))))) == True{} : Bool},
  +hw2: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SRP{Norm.line(P.btext(len, t, at, (j - at : U32)))}, Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), Norm.ms.line(o, Norm.rs_untick(s), qs, ql, Norm.LsR{Norm.line(P.btext(len, t, at, (j - at : U32)))}, back, Norm.Cx{P.mkSrcs(Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}), P.mkPd(pd), eof, dfs, True{}}, CD.mkWin(fa, wp))):
  (hql, m1) = mf
  (hxb, m2) = m1
  (hsb, m3) = m2
  (hout, m4) = m3
  rec_line(dfs, fa, T, cs, O, N, o, s, qs, ql, Norm.line(P.btext(len, t, at, (j - at : U32))), Con{P.SPP{len, t, d, at}, rest}, Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, asked, fneed,
    hRG, {==}, {==}, hmr, hr, hg, hx, hib, hn1, hone, hlt, hw2, hw3, hql, hxb, hsb, hout, hob, hb, hv)

# The next record of a buffer (its LF at j).
def msr_rec(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +j: U32,
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}))) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb.k(o, Norm.rs_untick(s), qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), dfs, True{})):
  (hsp0, r1) = sl
  (hn0, r2) = r1
  (hle0, hby0) = r2
  +hsp = {hsp0 : LI.SPLIT(len, t, d, at, j)}
  +hn = {hn0 : {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}}
  +hle = {hle0 : {U32.is_le((j + 1 : U32), len) == True{} : Bool}}
  +hby = {hby0 : {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}}
  +pp = MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +hc = MSX.wfC(fa, pp, hw)
  +m0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +MD = {S.MSP{s, qs, ql, None{}} : S.MdP}
  +AB = E.all_bytes(S.opts_args(o))
  +X = P.srctext(P.SPP{len, t, d, at})
  +RF0 = Bool.and(S.rtok(X), S.recs_first(rest))
  +RR0 = Bool.and(R.RunSt.inbody(S.smd(MD)), Nat.is_le(1n, R.RunSt.n(S.smd(MD))))
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +h01 = W.and_l(Bool.and(AB, RF0), RR0, h8)
  +hrr = W.and_r(Bool.and(AB, RF0), RR0, h8)
  +hrt = W.and_l(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, h01))
  +h1 = W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +hso = HX.srcs_head_p(rest, len, t, d, at, h1)
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +EP = String.is_empty(P.pdtext(pd))
  +A = P.btext(len, t, at, (j - at : U32))
  +l = Norm.line(A)
  +lt = B.Text.line(A)
  +S1 = P.srctext(P.SPP{len, t, d, (j + 1 : U32)})
  +hfit = {%Equal.sym(Nat, LI.n((j - at : U32)), Nat.sub(LI.n(j), LI.n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(j), LI.n(at))), LI.n(j), N.le_sub_add(LI.n(at), LI.n(j), hal)) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
    N.lt_to_le(LI.n(j), LI.n(len), hlt) : {Nat.is_le(Nat.add(LI.n(at), LI.n((j - at : U32))), LI.n(len)) == True{} : Bool}}
  +hls = HX.lines_sp(len, t, d, at, j, hsp, hn)
  +hlf0 = {%hsp : {S.ends_lf(_) == True{} : Bool}; W.and_l(S.ends_lf(X), S.all_one(B.Text.lines(X)), hrt) : {S.ends_lf(String.append(A, String.append("\n", S1))) == True{} : Bool}}
  +ho = {(%hls : {S.all_one(_) == True{} : Bool}; W.and_r(S.ends_lf(X), S.all_one(B.Text.lines(X)), hrt)) : {S.all_one(Con{lt, B.Text.lines(S1)}) == True{} : Bool}}
  +ho1 = W.and_l(S.one_alt(lt), S.all_one(B.Text.lines(S1)), ho)
  +hone = {(%Equal.sym(B.Line, Norm.line(A), B.Text.line(A), LN.line_eq(A)) : {Nat.is_lt(L.n_alts(B.Line.body(_)), 2n) == True{} : Bool}; ho1) : {Nat.is_lt(L.n_alts(B.Line.body(l)), 2n) == True{} : Bool}}
  +hlt2 = {(%Equal.sym(String, B.Line.text(l), String.append(A, "\n"), CS.ltext_nl(A)) : {E.is_bytes(_) == True{} : Bool}; LSS.bytes_app(A, "\n", hby, {==})) : {E.is_bytes(B.Line.text(l)) == True{} : Bool}}
  +hlfl = {(%Equal.sym(String, B.Line.text(l), String.append(A, "\n"), CS.ltext_nl(A)) : {S.ends_lf(_) == True{} : Bool}; lf_nl(A)) : {S.ends_lf(B.Line.text(l)) == True{} : Bool}}
  +hlf1 = T.lf_suf("\n", S1, T.lf_suf(A, String.append("\n", S1), hlf0))
  +q2 = MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, 0n, wp, None{}, False{})
  +hw2 = Equal.trans(Bool, S.WF(fa, q2), W.C9(W.W0(fa, q2), W.W1(fa, q2), W.W2(fa, q2), W.W3(fa, q2), W.W4(fa, q2), W.W5(fa, q2), W.W6(fa, q2), W.W7(fa, q2), W.W8(fa, q2)), True{}, W.wf_c9(fa, q2),
    W.c9_mk(W.W0(fa, q2), W.W1(fa, q2), W.W2(fa, q2), W.W3(fa, q2), W.W4(fa, q2), W.W5(fa, q2), W.W6(fa, q2), W.W7(fa, q2), W.W8(fa, q2),
      W.c9_0(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), HX.srcs_next_p(rest, len, t, d, at, j, hsp, hle, h1), W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      HX.eof_next_p(eof, rest, pd, len, t, d, at, j, hsp, W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)), W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.and_tt(Bool.and(AB, Bool.and(S.rtok(S1), S.recs_first(rest))), RR0,
        W.and_tt(AB, Bool.and(S.rtok(S1), S.recs_first(rest)), W.and_l(AB, RF0, h01),
          W.and_tt(S.rtok(S1), S.recs_first(rest), W.and_tt(S.ends_lf(S1), S.all_one(B.Text.lines(S1)), hlf1, W.and_r(S.one_alt(lt), S.all_one(B.Text.lines(S1)), ho)),
            W.and_r(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, h01)))),
        hrr)))
  +hw3 = wf_pre_rec(dfs, fa, o, s, qs, ql, l, P.SPP{len, t, d, (j + 1 : U32)}, rest, pd, eof, wp, hw2, hlt2, hlfl, hone, W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc), hrr)
  %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), A), MSX.sb_text(len, t, d, at, (j - at : U32), hok, hfit)) :
    S.AdvG(fa, T, cs, O, N, pp, Norm.ms.sb.k(o, Norm.rs_untick(s), qs, ql, at, j, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), dfs, True{}))
  msr_rec.k(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, j, MSX.md_facts(s, qs, ql, W.c9_0(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)), rr_ib(s, qs, ql, hrr), rr_n(s, qs, ql, hrr),
    X2 => {(%Equal.sym(List<&2, B.Line>, B.Text.lines(X), Con{lt, B.Text.lines(S1)}, hls) :
          {S.RG(S.recs(rest), fa, dfs, o, S.rgo(_, fa, dfs, o, X2)) == S.RG(S.recs(rest), fa, dfs, o, S.rgo(B.Text.lines(S1), fa, dfs, o, S.rstep(fa, dfs, o, X2, l))) : R.RunSt};
        %Equal.sym(B.Line, Norm.line(A), B.Text.line(A), LN.line_eq(A)) : {S.RG(S.recs(rest), fa, dfs, o, S.rgo(B.Text.lines(S1), fa, dfs, o, S.rstep(fa, dfs, o, X2, lt))) == S.RG(S.recs(rest), fa, dfs, o, S.rgo(B.Text.lines(S1), fa, dfs, o, S.rstep(fa, dfs, o, X2, _))) : R.RunSt};
        {==}) : {S.RG(S.recs(Con{P.SPP{len, t, d, at}, rest}), fa, dfs, o, X2) == S.RG(S.recs(Con{P.SPP{len, t, d, (j + 1 : U32)}, rest}), fa, dfs, o, S.rstep(fa, dfs, o, X2, l)) : R.RunSt}},
    mrec_sp(len, t, d, at, j, rest, hal, hlt, hle, hs, LP.inc_len(len, t, d, j, hok, hlt)),
    hone, hlt2, hw2, hw3, W.and_l(AB, RF0, h01), W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc))

def msr_if(+dfs: B.Defs, +part: Bool, +j: U32, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hjf: {LI.n(j) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool},
  +hl0: {U32.is_le(len, at) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb.if(part, o, Norm.rs_untick(s), qs, ql, C.BT(len, t), at, j, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed, dfs, True{})):
  match part:
    case True{}:
    +pp = MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
    +hc = MSX.wfC(fa, pp, hw)
    +m0 = W.W0(fa, pp)
    +a1 = W.W1(fa, pp)
    +a2 = W.W2(fa, pp)
    +a3 = W.W3(fa, pp)
    +a4 = W.W4(fa, pp)
    +a5 = W.W5(fa, pp)
    +a6 = W.W6(fa, pp)
    +a7 = W.W7(fa, pp)
    +a8 = W.W8(fa, pp)
    +MD = {S.MSP{s, qs, ql, None{}} : S.MdP}
    +AB = E.all_bytes(S.opts_args(o))
    +X = P.srctext(P.SPP{len, t, d, at})
    +RF0 = Bool.and(S.rtok(X), S.recs_first(rest))
    +RR0 = Bool.and(R.RunSt.inbody(S.smd(MD)), Nat.is_le(1n, R.RunSt.n(S.smd(MD))))
    +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
    +h01 = W.and_l(Bool.and(AB, RF0), RR0, h8)
    +hrr = W.and_r(Bool.and(AB, RF0), RR0, h8)
    +hrt = W.and_l(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, h01))
    +h1 = W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
    +hso = HX.srcs_head_p(rest, len, t, d, at, h1)
    +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
    +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
    +EP = String.is_empty(P.pdtext(pd))
      +hjl = {%U.is_eq_true(j, len, ep) : {LI.n(_) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}; hjf : {LI.n(len) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}}
      Empty.absurd(S.AdvG(fa, T, cs, O, N, pp,
          Norm.ms.sb.if(True{}, o, Norm.rs_untick(s), qs, ql, C.BT(len, t), at, j, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed, dfs, True{})),
        HX.part_sp.k(len, t, d, at, hok, HX.ult(len, at, hl0), W.and_l(S.ends_lf(X), S.all_one(B.Text.lines(X)), hrt),
          LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, LI.n(len), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjl))))
    case False{}:
    +pp = MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
    +hc = MSX.wfC(fa, pp, hw)
    +m0 = W.W0(fa, pp)
    +a1 = W.W1(fa, pp)
    +a2 = W.W2(fa, pp)
    +a3 = W.W3(fa, pp)
    +a4 = W.W4(fa, pp)
    +a5 = W.W5(fa, pp)
    +a6 = W.W6(fa, pp)
    +a7 = W.W7(fa, pp)
    +a8 = W.W8(fa, pp)
    +MD = {S.MSP{s, qs, ql, None{}} : S.MdP}
    +AB = E.all_bytes(S.opts_args(o))
    +X = P.srctext(P.SPP{len, t, d, at})
    +RF0 = Bool.and(S.rtok(X), S.recs_first(rest))
    +RR0 = Bool.and(R.RunSt.inbody(S.smd(MD)), Nat.is_le(1n, R.RunSt.n(S.smd(MD))))
    +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
    +h01 = W.and_l(Bool.and(AB, RF0), RR0, h8)
    +hrr = W.and_r(Bool.and(AB, RF0), RR0, h8)
    +hrt = W.and_l(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, h01))
    +h1 = W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
    +hso = HX.srcs_head_p(rest, len, t, d, at, h1)
    +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
    +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
    +EP = String.is_empty(P.pdtext(pd))
      +hjr = MSX.sb_jr(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr)
      +hlt = MSX.sb_jlt(len, j, W.and_r(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr), ep)
      msr_rec(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, j, hal, hlt, LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjf), hlt))

def msr_j(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hl0: {U32.is_le(len, at) == False{} : Bool},
  ex: MSX.SBW(len, t, at)) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb(o, Norm.rs_untick(s), qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed, dfs, True{})):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
              Norm.ms.sb(o, Norm.rs_untick(s), qs, ql, at, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed, dfs, True{}))
          msr_if(dfs, U32.is_eq(j, len), j, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hjf, {==}, hl0)

def msr_spif(+dn: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +edn: {U32.is_le(len, at) == dn : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.sp.s.if(dn, o, s, qs, ql, C.BT(len, t), at, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), asked, fneed, dfs)):
  match dn:
    case True{}:
      msr_done(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, edn)
    case False{}:
      +pp = MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
      +hc = MSX.wfC(fa, pp, hw)
      +hso = HX.srcs_head_p(rest, len, t, d, at, W.c9_1(W.W0(fa, pp), W.W1(fa, pp), W.W2(fa, pp), W.W3(fa, pp), W.W4(fa, pp), W.W5(fa, pp), W.W6(fa, pp), W.W7(fa, pp), W.W8(fa, pp), hc))
      +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
      +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
      msr_j(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, edn, LN.lf_ok(len, t, d, at, hok, hs))

# A record buffer in the String mode (proof_b_adv.bend's mssrc).
def ms_spp(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, MSX.SO(dfs, o, s, qs, ql, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.sp.s(o, s, qs, ql, BY.len(C.BT(len, t)), at, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), asked, fneed, dfs)):
  msr_spif(U32.is_le(len, at), dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, {==})
