import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_split.bend as NS
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_frame.bend as FR
import ./proof_b_frame_fr.bend as FF
import ./proof_b_rundefs.bend as RD
import ./proof_b_lines_str.bend as LSS
import ./proof_b_adv_line.bend as LI
import ./proof_s_recs.bend as RS
import ./proof_s_inj.bend as INJ
import ./proof_s_one.bend as OI
import ./proof_b_adv_str.bend as T
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_wr.bend as WR
import lawful-fields@0.1.0.0/defs.bend as FD
import ./proof_b_run.bend as PR
import ./proof_b_lines.bend as LN
import ./proof_b_adv_nat.bend as LP
import ./proof_b_mw.bend as MW
import ./proof_s_ck.bend as CK
import ./proof_s_drv.bend as DR
import ./proof_s_line.bend as SL
import ./proof_s_term.bend as TC
import ./proof_s_w.bend as SW
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C

# The byte splitter's branch of the byte mode (norm_seq.bend's split.b,
# split.out, inject): a line with a comma in ALT, split on its bytes, puts
# its records in front of the rest of the input (an SP source), and the run
# ticked for the line; the records, handled one by one later, give what the
# spec gives the line. Every variable is reusable.

def Ls() -> Data:
  List<&2, B.Line>

# A run in the body stays in the body.
def ib_ls.k(+dfs: B.Defs, +xh: Bool, +i: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o0: String, +ns: List<&2, B.Note>, +l: B.Line,
  +hi: {i == True{} : Bool}) ->
  {R.RunSt.inbody(L.line_step(fa, dfs, o, R.RunSt{n, i, h, c, e, la, b, k, o0, ns, xh}, l)) == True{} : Bool}:
  match xh i:
    case True{} _:
      hi
    case False{} True{}:
      +fs = B.Rec.fields(B.Line.body(l))
      FF.ib_body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, R.RunSt{1n+n, True{}, h, c, e, la, b, k, o0, ns, False{}}, o, l, B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))
    case False{} False{}:
      Empty.absurd({R.RunSt.inbody(L.line_step(fa, dfs, o, R.RunSt{n, False{}, h, c, e, la, b, k, o0, ns, False{}}, l)) == True{} : Bool}, N.false_ne_true(hi))

def ib_ls(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +l: B.Line, +hi: {R.RunSt.inbody(s) == True{} : Bool}) ->
  {R.RunSt.inbody(L.line_step(fa, dfs, o, s, l)) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o0, +ns, +xh}:
      ib_ls.k(dfs, xh, i, fa, o, n, h, c, e, la, b, k, o0, ns, l, hi)

# The records' steps, from a run in the body: O and N in front go through.
law rgo_pre:
  for +ls: Ls()
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +hi: {R.RunSt.inbody(st) == True{} : Bool}
  {S.rgo(ls, fa, dfs, o, S.pre(O, N, st)) == S.pre(O, N, S.rgo(ls, fa, dfs, o, st)) : R.RunSt}

def rgo_pre(ls, fa, dfs, o, O, N, st, hi):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      match st:
        case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
          match x:
            case True{}:
              rgo_pre(t, fa, dfs, o, O, N, R.RunSt{n, i, h, c, e, la, b, k, so, ns, True{}}, hi)
            case False{}:
              +u = {R.RunSt{Nat.sub(n, 1n), i, h, c, e, la, b, k, so, ns, False{}} : R.RunSt}
              %Equal.sym(R.RunSt, L.line_step(fa, dfs, o, S.pre(O, N, u), l), S.pre(O, N, L.line_step(fa, dfs, o, u, l)), FR.step_pre(dfs, fa, o, O, N, u, l, {%Equal.sym(Bool, i, True{}, hi) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}; {==} : {Bool.or(i, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}})) :
                {S.rgo(t, fa, dfs, o, _) == S.pre(O, N, S.rgo(t, fa, dfs, o, L.line_step(fa, dfs, o, u, l))) : R.RunSt}
              rgo_pre(t, fa, dfs, o, O, N, L.line_step(fa, dfs, o, u, l), ib_ls(dfs, fa, o, u, l, hi))

# ---------------------------------------------------------------------------
# The state after the records are put in front
# ---------------------------------------------------------------------------

def StM(+dfs: B.Defs, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}

# The records' buffer (from its start).
def SPQ(+l2: U32, +t2: AT.Tree<U32>) -> P.SrcP:
  P.SPP{l2, t2, RD.tdepth(t2), 0}

def Q2(+dfs: B.Defs, +o: B.Opts, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +lf: U32, +l2: U32, +t2: AT.Tree<U32>, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: PC.WP) -> S.StP:
  StM(dfs, o, S.MBP{rp1}, Con{SPQ(l2, t2), Con{P.SBP{len, t, d, (lf + 1 : U32)}, rest}}, pd, eof, 0n, wp, None{}, False{})

def ib_tick(+st: R.RunSt) -> {R.RunSt.inbody(R.tick(st)) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

def halt_tick(+st: R.RunSt) -> {R.RunSt.halt(R.tick(st)) == R.RunSt.halt(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

# The report: the records, one by one from the ticked run, stand for the
# line they came from.
def rep_inj(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +l2: U32, +t2: AT.Tree<U32>, +ps: List<&2, String>,
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +hp: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts},
  +hl: {B.Text.lines(P.srctext(SPQ(l2, t2))) == RS.LS(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : Ls()}) ->
  {S.report(fa, cs, O, N, Q2(dfs, o, rp1, len, t, d, lf, l2, t2, rest, pd, eof, wp)) == T : R.Report}:
  +p = StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +q = Q2(dfs, o, rp1, len, t, d, lf, l2, t2, rest, pd, eof, wp)
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +tm = B.Line.term(l)
  +IT2 = S.intext(q, cs)
  +LS2 = B.Text.lines(IT2)
  +LSP = B.Text.lines(S.intext(p, cs))
  +st = P.specRun(rp)
  +hib = Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, LI.ib_spec(rp), hin)
  +hit = Equal.trans(Bool, R.RunSt.inbody(R.tick(st)), R.RunSt.inbody(st), True{}, ib_tick(st), hib)
  +hxt = Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, LI.halt_spec(rp), hx)
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st), s1) :
    {R.finish(L.run.go(LS2, fa, L.defs.go(LS2, R.RunSt.inbody(_), dfs), o, S.rgo(B.Text.lines(P.srctext(SPQ(l2, t2))), fa, L.defs.go(LS2, R.RunSt.inbody(_), dfs), o, S.pre(O, N, _)))) == T : R.Report}
  %Equal.sym(Bool, R.RunSt.inbody(R.tick(st)), True{}, hit) :
    {R.finish(L.run.go(LS2, fa, L.defs.go(LS2, _, dfs), o, S.rgo(B.Text.lines(P.srctext(SPQ(l2, t2))), fa, L.defs.go(LS2, _, dfs), o, S.pre(O, N, R.tick(st))))) == T : R.Report}
  %Equal.sym(B.Defs, L.defs.go(LS2, True{}, dfs), dfs, FF.defs_done(LS2, dfs)) :
    {R.finish(L.run.go(LS2, fa, _, o, S.rgo(B.Text.lines(P.srctext(SPQ(l2, t2))), fa, _, o, S.pre(O, N, R.tick(st))))) == T : R.Report}
  %Equal.sym(Ls(), B.Text.lines(P.srctext(SPQ(l2, t2))), RS.LS(ps, tm), hl) :
    {R.finish(L.run.go(LS2, fa, dfs, o, S.rgo(_, fa, dfs, o, S.pre(O, N, R.tick(st))))) == T : R.Report}
  %Equal.sym(R.RunSt, S.rgo(RS.LS(ps, tm), fa, dfs, o, S.pre(O, N, R.tick(st))), S.pre(O, N, S.rgo(RS.LS(ps, tm), fa, dfs, o, R.tick(st))), rgo_pre(RS.LS(ps, tm), fa, dfs, o, O, N, R.tick(st), hit)) :
    {R.finish(L.run.go(LS2, fa, dfs, o, _)) == T : R.Report}
  %Equal.sym(R.RunSt, S.rgo(RS.LS(ps, tm), fa, dfs, o, R.tick(st)), L.line_step(fa, dfs, o, st, l), INJ.rgo_line(fa, dfs, dfs, o, st, l, ps, hxt, hib, hp)) :
    {R.finish(L.run.go(LS2, fa, dfs, o, S.pre(O, N, _))) == T : R.Report}
  %FR.step_pre(dfs, fa, o, O, N, st, l, {%Equal.sym(Bool, R.RunSt.inbody(st), True{}, hib) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}; {==} : {Bool.or(R.RunSt.inbody(st), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}}) :
    {R.finish(L.run.go(LS2, fa, dfs, o, _)) == T : R.Report}
  +elines = Equal.trans(Ls(), LSP, B.Text.lines(String.append(A, String.append("\n", IT2))), Con{l, LS2},
    Equal.cong(String, Ls(), x => B.Text.lines(x), S.intext(p, cs), String.append(A, String.append("\n", IT2)),
      Equal.sym(String, String.append(A, String.append("\n", IT2)), S.intext(p, cs),
        LI.itx(dfs, o, S.MBP{rp}, S.MBP{rp1}, rest, pd, eof, back, 0n, wp, asked, None{}, fneed, False{}, cs, len, t, d, at, lf, hs))),
    LSS.lines_cons(A, IT2, hn))
  %elines : {R.finish(L.run.go(_, fa, dfs, o, S.pre(O, N, st))) == T : R.Report}
  %Equal.trans(B.Defs, L.defs.go(LSP, R.RunSt.inbody(st), dfs), L.defs.go(LSP, True{}, dfs), dfs, Equal.cong(Bool, B.Defs, z => L.defs.go(LSP, z, dfs), R.RunSt.inbody(st), True{}, hib), FF.defs_done(LSP, dfs)) :
    {R.finish(L.run.go(LSP, fa, _, o, S.pre(O, N, st))) == T : R.Report}
  hr

# ---------------------------------------------------------------------------
# Texts ending with LF (S.ends_lf: empty, or ending with an LF)
# ---------------------------------------------------------------------------

def lf_ne(+y: String, +hy: {S.ends_lf(y) == True{} : Bool}, +hne: {String.is_empty(y) == False{} : Bool}) -> {T.ends_nl(y) == True{} : Bool}:
  +OR = Bool.or(String.is_empty(y), T.ends_nl(y))
  +h2 = Equal.trans(Bool, OR, S.ends_lf(y), True{}, Equal.sym(Bool, S.ends_lf(y), OR, T.lf_eq(y)), hy)
  Equal.trans(Bool, T.ends_nl(y), OR, True{},
    {%Equal.sym(Bool, String.is_empty(y), False{}, hne) : {T.ends_nl(y) == Bool.or(_, T.ends_nl(y)) : Bool}; {==} : {T.ends_nl(y) == OR : Bool}}, h2)

# x then y (y not empty, ending with LF).
def lf_pre(+x: String, +y: String, +hy: {S.ends_lf(y) == True{} : Bool}, +hne: {String.is_empty(y) == False{} : Bool}) ->
  {S.ends_lf(String.append(x, y)) == True{} : Bool}:
  %Equal.sym(Bool, S.ends_lf(String.append(x, y)), Bool.or(String.is_empty(String.append(x, y)), T.ends_nl(String.append(x, y))), T.lf_eq(String.append(x, y))) : {_ == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(String.append(x, y)), False{}, T.app_ne(x, y, hne)) : {Bool.or(_, T.ends_nl(String.append(x, y))) == True{} : Bool}
  %Equal.sym(Bool, T.ends_nl(String.append(x, y)), T.ends_nl(y), T.nl_app(x, y, hne)) : {Bool.or(False{}, _) == True{} : Bool}
  lf_ne(y, hy, hne)

# Both ending with LF.
law lf_app:
  for +x: String
  for +y: String
  for +hx: {S.ends_lf(x) == True{} : Bool}
  for +hy: {S.ends_lf(y) == True{} : Bool}
  {S.ends_lf(String.append(x, y)) == True{} : Bool}

def lf_app(x, y, hx, hy):
  match y:
    case SNil{}:
      %Equal.sym(String, String.append(x, ""), x, LSS.sapp_nil(x)) : {S.ends_lf(_) == True{} : Bool}
      hx
    case SCon{+c, +t}:
      lf_pre(x, SCon{c, t}, hy, {==})

def ne_app(+x: String, +y: String, +hx: {String.is_empty(x) == False{} : Bool}) -> {String.is_empty(String.append(x, y)) == False{} : Bool}:
  match x:
    case SNil{}:
      Empty.absurd({String.is_empty(y) == False{} : Bool}, W.ft(Equal.sym(Bool, True{}, False{}, hx)))
    case SCon{+c, +t}:
      {==}

# The records' text ends with LF (the terminator does).
law lf_recs:
  for +ps: List<&2, String>
  for +term: String
  for +ht: {S.ends_lf(term) == True{} : Bool}
  for +hne: {String.is_empty(term) == False{} : Bool}
  {S.ends_lf(Norm.recs_text(ps, term)) == True{} : Bool}

def lf_recs(ps, term, ht, hne):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +R = Norm.recs_text(t, term)
      lf_pre(p, String.append(term, R), lf_app(term, R, ht, lf_recs(t, term, ht, hne)), ne_app(term, R, hne))

# ---------------------------------------------------------------------------
# The state after: good
# ---------------------------------------------------------------------------

def SB(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32) -> P.SrcP:
  P.SBP{len, t, d, at}

def le0(+x: U32) -> {U32.is_le(0, x) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(0, x), Nat.is_le(U32.to_nat(0), U32.to_nat(x)), True{}, U.is_le_to_nat(0, x), N.le_zero_l(U32.to_nat(x)))

# The sources: the records' buffer (good, its text ending with LF), then
# the buffer past the line.
def srcs_inj(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +l2: U32, +t2: AT.Tree<U32>,
  +hs: LI.SPLIT(len, t, d, at, lf), +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +h1: {S.srcs_ok(Con{SB(len, t, d, at), rest}) == True{} : Bool},
  +hok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool},
  +hlf: {S.ends_lf(P.srctext(SPQ(l2, t2))) == True{} : Bool}) ->
  {S.srcs_ok(Con{SPQ(l2, t2), Con{SB(len, t, d, (lf + 1 : U32)), rest}}) == True{} : Bool}:
  W.and_tt(Bool.and(P.src_ok(SPQ(l2, t2)), S.ends_lf(P.srctext(SPQ(l2, t2)))), S.srcs_ok(Con{SB(len, t, d, (lf + 1 : U32)), rest}),
    W.and_tt(P.src_ok(SPQ(l2, t2)), S.ends_lf(P.srctext(SPQ(l2, t2))),
      W.and_tt(D.ok(C.BT(l2, t2), RD.tdepth(t2)), U32.is_le(0, l2), hok2, le0(l2)), hlf),
    LI.srcs_next(rest, len, t, d, at, lf, hs, hle, h1))

# After the end of the file: the sources' text ends with LF.
def eof_inj(+eof: Bool, +pd: P.PdP, +x: String, +y: String,
  +hx: {S.ends_lf(x) == True{} : Bool},
  +h: {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(y))) == True{} : Bool}) ->
  {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(x, y)))) == True{} : Bool}:
  match eof:
    case False{}:
      {==}
    case True{}:
      W.and_tt(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(x, y)), W.and_l(String.is_empty(P.pdtext(pd)), S.ends_lf(y), h),
        lf_app(x, y, hx, W.and_r(String.is_empty(P.pdtext(pd)), S.ends_lf(y), h)))

def wf_inj(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +l2: U32, +t2: AT.Tree<U32>,
  +hw: {S.WF(fa, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hs: LI.SPLIT(len, t, d, at, lf), +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +i1: {S.md_ok(S.MBP{rp1}) == True{} : Bool},
  +hok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool},
  +hlf: {S.ends_lf(P.srctext(SPQ(l2, t2))) == True{} : Bool},
  +hone: {S.all_one(B.Text.lines(P.srctext(SPQ(l2, t2)))) == True{} : Bool},
  +hrr: {S.recs_run(S.MBP{rp1}, Con{SPQ(l2, t2), Con{SB(len, t, d, (lf + 1 : U32)), rest}}) == True{} : Bool}) ->
  {S.WF(fa, Q2(dfs, o, rp1, len, t, d, lf, l2, t2, rest, pd, eof, wp)) == True{} : Bool}:
  +p = StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +q = Q2(dfs, o, rp1, len, t, d, lf, l2, t2, rest, pd, eof, wp)
  +m0 = S.md_ok(S.MBP{rp})
  +a1 = W.W1(fa, p)
  +a2 = W.W2(fa, p)
  +a3 = W.W3(fa, p)
  +a4 = W.W4(fa, p)
  +a5 = W.W5(fa, p)
  +a6 = W.W6(fa, p)
  +a7 = W.W7(fa, p)
  +a8 = W.W8(fa, p)
  +AB = E.all_bytes(S.opts_args(o))
  +NR0 = S.no_recs(rest)
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +hab = W.and_l(Bool.and(AB, NR0), S.recs_run(S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}), h8)
  +LF = S.rtok(P.srctext(SPQ(l2, t2)))
  +b8 = W.and_tt(Bool.and(AB, Bool.and(LF, NR0)), S.recs_run(S.MBP{rp1}, Con{SPQ(l2, t2), Con{SB(len, t, d, (lf + 1 : U32)), rest}}),
    W.and_tt(AB, Bool.and(LF, NR0), W.and_l(AB, NR0, hab),
      W.and_tt(LF, NR0, W.and_tt(S.ends_lf(P.srctext(SPQ(l2, t2))), S.all_one(B.Text.lines(P.srctext(SPQ(l2, t2)))), hlf, hone), W.and_r(AB, NR0, hab))), hrr)
  W.c9_mk(S.md_ok(S.MBP{rp1}), W.W1(fa, q), a2, a3, a4, W.W5(fa, q), a6, a7, W.W8(fa, q), i1,
    srcs_inj(len, t, d, at, lf, rest, l2, t2, hs, hle, W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), hok2, hlf),
    W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw),
    eof_inj(eof, pd, P.srctext(SPQ(l2, t2)), P.srcstext(Con{SB(len, t, d, (lf + 1 : U32)), rest}), hlf,
      LI.eof_next(eof, rest, pd, len, t, d, at, lf, hs, W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw))),
    W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), b8)

# ---------------------------------------------------------------------------
# The records put in front: Went
# ---------------------------------------------------------------------------

# Both states' definitions are the run's: the text after them is the body.
def defs_ib(+ls: Ls(), +dfs: B.Defs, +i: Bool, +hi: {i == True{} : Bool}) -> {L.defs.go(ls, i, dfs) == dfs : B.Defs}:
  %Equal.sym(Bool, i, True{}, hi) : {L.defs.go(ls, _, dfs) == dfs : B.Defs}
  FF.defs_done(ls, dfs)

def defs_in2(+a: B.Defs, +b: B.Defs, +c: B.Defs, +ha: {a == c : B.Defs}, +hb: {b == c : B.Defs}) -> {a == b : B.Defs}:
  Equal.trans(B.Defs, a, c, b, ha, Equal.sym(B.Defs, b, c, hb))

def moved_inj(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +l2: U32, +t2: AT.Tree<U32>, +ps: List<&2, String>,
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +hp: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts},
  +hl: {B.Text.lines(P.srctext(SPQ(l2, t2))) == RS.LS(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : Ls()}) ->
  S.Moved(fa, cs, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), Q2(dfs, o, rp1, len, t, d, lf, l2, t2, rest, pd, eof, wp)):
  +p = StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +q = Q2(dfs, o, rp1, len, t, d, lf, l2, t2, rest, pd, eof, wp)
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +tm = B.Line.term(l)
  +IT2 = S.intext(q, cs)
  +LSP = B.Text.lines(S.intext(p, cs))
  +st = P.specRun(rp)
  +hib = Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, LI.ib_spec(rp), hin)
  +hxt = Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, LI.halt_spec(rp), hx)
  +eD = Equal.trans(B.Defs, L.defs.go(LSP, R.RunSt.inbody(st), dfs), L.defs.go(LSP, True{}, dfs), dfs, Equal.cong(Bool, B.Defs, z => L.defs.go(LSP, z, dfs), R.RunSt.inbody(st), True{}, hib), FF.defs_done(LSP, dfs))
  (Con{l, Nil{}},
    (Equal.trans(Ls(), LSP, B.Text.lines(String.append(A, String.append("\n", IT2))), Con{l, B.Text.lines(IT2)},
      Equal.cong(String, Ls(), x => B.Text.lines(x), S.intext(p, cs), String.append(A, String.append("\n", IT2)),
        Equal.sym(String, String.append(A, String.append("\n", IT2)), S.intext(p, cs),
          LI.itx(dfs, o, S.MBP{rp}, S.MBP{rp1}, rest, pd, eof, back, 0n, wp, asked, None{}, fneed, False{}, cs, len, t, d, at, lf, hs))),
      LSS.lines_cons(A, IT2, hn)),
    {%Equal.sym(B.Defs, L.defs.go(LSP, R.RunSt.inbody(st), dfs), dfs, eD) :
       {P.settle(S.rgo(B.Text.lines(P.srctext(SPQ(l2, t2))), fa, _, o, P.specRun(rp1))) == P.settle(L.line_step(fa, _, o, st, l)) : R.RunSt};
     %Equal.sym(Ls(), B.Text.lines(P.srctext(SPQ(l2, t2))), RS.LS(ps, tm), hl) :
       {P.settle(S.rgo(_, fa, dfs, o, P.specRun(rp1))) == P.settle(L.line_step(fa, dfs, o, st, l)) : R.RunSt};
     %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st), s1) :
       {P.settle(S.rgo(RS.LS(ps, tm), fa, dfs, o, _)) == P.settle(L.line_step(fa, dfs, o, st, l)) : R.RunSt};
     %Equal.sym(R.RunSt, S.rgo(RS.LS(ps, tm), fa, dfs, o, R.tick(st)), L.line_step(fa, dfs, o, st, l), INJ.rgo_line(fa, dfs, dfs, o, st, l, ps, hxt, hib, hp)) :
       {P.settle(_) == P.settle(L.line_step(fa, dfs, o, st, l)) : R.RunSt};
     {==} : {P.settle(S.RG(S.recs(S.StP.src(q)), fa, S.DEFS(p, cs), o, P.specRun(rp1))) == P.settle(L.run.go(Con{l, Nil{}}, fa, S.DEFS(p, cs), o, S.RG(S.recs(S.StP.src(p)), fa, S.DEFS(p, cs), o, P.specRun(rp)))) : R.RunSt}},
    defs_in2(S.DEFS(q, cs), S.DEFS(p, cs), dfs,
      defs_ib(B.Text.lines(IT2), dfs, R.RunSt.inbody(P.specRun(rp1)),
        Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp1)), R.RunSt.inbody(R.tick(st)), True{}, Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.specRun(rp1), R.tick(st), s1),
          Equal.trans(Bool, R.RunSt.inbody(R.tick(st)), R.RunSt.inbody(st), True{}, ib_tick(st), hib))),
      eD)))

def SPR0(+len: U32, +t: AT.Tree<U32>, +lf: U32, +l2: U32, +t2: AT.Tree<U32>, +rest: List<&2, P.SrcP>) -> List<&1, Norm.Src>:
  Con{Norm.SP{C.BT(l2, t2), 0}, Con{Norm.SB{C.BT(len, t), (lf + 1 : U32)}, P.mkSrcs(rest)}}

law went_inj:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +rp1: P.RunP
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +lf: U32
  for +rest: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +l2: U32
  for +t2: AT.Tree<U32>
  for +ps: List<&2, String>
  for +hw: {S.WF(fa, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report}
  for +hg: {S.guard(O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool}
  for +hs: LI.SPLIT(len, t, d, at, lf)
  for +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool}
  for +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool}
  for +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool}
  for +hat: {U32.is_le(at, len) == True{} : Bool}
  for +hinc: {U32.to_nat((lf + 1 : U32)) == Nat.add(U32.to_nat(lf), 1n) : Nat}
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  for +hin: {P.RunP.i(rp) == True{} : Bool}
  for +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run}
  for +i1: {S.md_ok(S.MBP{rp1}) == True{} : Bool}
  for +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt}
  for +hp: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts}
  for +hl: {B.Text.lines(P.srctext(SPQ(l2, t2))) == RS.LS(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : Ls()}
  for +hok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool}
  for +hlf: {S.ends_lf(P.srctext(SPQ(l2, t2))) == True{} : Bool}
  for +hrr: {S.recs_run(S.MBP{rp1}, Con{SPQ(l2, t2), Con{SB(len, t, d, (lf + 1 : U32)), rest}}) == True{} : Bool}
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{NR.tick(P.mkRun(rp))}, SPR0(len, t, lf, l2, t2, rest), P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}})

def went_inj(dfs, fa, T, cs, O, N, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, l2, t2, ps, hw, hr, hg, hs, hn, hle, hal, hlt, hat, hinc, hx, hin, et, i1, s1, hp, hl, hok2, hlf, hrr):
  +p = StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +q = Q2(dfs, o, rp1, len, t, d, lf, l2, t2, rest, pd, eof, wp)
  +st = P.specRun(rp)
  +hib = Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, LI.ib_spec(rp), hin)
  +hit = Equal.trans(Bool, R.RunSt.inbody(R.tick(st)), R.RunSt.inbody(st), True{}, ib_tick(st), hib)
  +hg1 = {%Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st), s1) : {Bool.or(R.RunSt.inbody(_), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
    %Equal.sym(Bool, R.RunSt.inbody(R.tick(st)), True{}, hit) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
    {==} : {S.guard(O, N, q) == True{} : Bool}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    S.AdvG(fa, T, cs, O, N, p, Norm.Went{Norm.St{o, Norm.MB{_}, SPR0(len, t, lf, l2, t2, rest), P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}})
  (q, ({==}, (wf_inj(dfs, fa, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, l2, t2, hw, hs, hle, i1, hok2, hlf, {(%Equal.sym(Ls(), B.Text.lines(P.srctext(SPQ(l2, t2))), RS.LS(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), hl) : {S.all_one(_) == True{} : Bool}; OI.pieces_one(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), hp)) : {S.all_one(B.Text.lines(P.srctext(SPQ(l2, t2)))) == True{} : Bool}}, hrr),
    (rep_inj(dfs, fa, T, cs, O, N, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, l2, t2, ps, hr, hg, hs, hn, hx, hin, s1, hp, hl),
    (W.less_lt(q, p, LI.meas_line(dfs, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hal, hlt, hle, hat, hinc)),
    ({==}, ({==}, (hg1, ({==},
    (moved_inj(dfs, fa, cs, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, l2, t2, ps, hs, hn, hx, hin, s1, hp, hl),
     hk => ((lf + 1 : U32), {==})))))))))))

# ---------------------------------------------------------------------------
# The byte splitter's branch
# ---------------------------------------------------------------------------

def n_tick(+s0: R.RunSt) -> {R.RunSt.n(R.tick(s0)) == 1n+R.RunSt.n(s0) : Nat}:
  match s0:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

def tlf(+cr: Bool) -> {S.ends_lf(Bool.pick(String, cr, "\r\n", "\n")) == True{} : Bool}:
  match cr:
    case True{}:
      {==}
    case False{}:
      {==}

def tne(+cr: Bool) -> {String.is_empty(Bool.pick(String, cr, "\r\n", "\n")) == False{} : Bool}:
  match cr:
    case True{}:
      {==}
    case False{}:
      {==}

# While the records wait, the run is in the body and has counted their line.
def rr_inj(+rp: P.RunP, +rp1: P.RunP, +l2: U32, +t2: AT.Tree<U32>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +lf: U32, +rest: List<&2, P.SrcP>,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +hit: {R.RunSt.inbody(R.tick(P.specRun(rp))) == True{} : Bool}) ->
  {S.recs_run(S.MBP{rp1}, Con{SPQ(l2, t2), Con{SB(len, t, d, (lf + 1 : U32)), rest}}) == True{} : Bool}:
  +st0 = P.specRun(rp)
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st0), s1) :
    {Bool.or(False{}, Bool.and(R.RunSt.inbody(_), Nat.is_le(1n, R.RunSt.n(_)))) == True{} : Bool}
  %Equal.sym(Bool, R.RunSt.inbody(R.tick(st0)), True{}, hit) : {Bool.or(False{}, Bool.and(_, Nat.is_le(1n, R.RunSt.n(R.tick(st0))))) == True{} : Bool}
  %Equal.sym(Nat, R.RunSt.n(R.tick(st0)), 1n+R.RunSt.n(st0), n_tick(st0)) : {Bool.or(False{}, Bool.and(True{}, Nat.is_le(1n, _))) == True{} : Bool}
  N.le_zero_l(R.RunSt.n(st0))

# The records' buffer's text from its start.
def spq_txt(+l2: U32, +t2: AT.Tree<U32>) -> {P.srctext(SPQ(l2, t2)) == NR.chars(SW.V(l2, t2)) : String}:
  Equal.cong(List<&2, U32>, String, xs => NR.chars(xs), List.drop(&2, U32, SW.V(l2, t2), 0n), SW.V(l2, t2), CK.drop0(SW.V(l2, t2)))

def inj.tk2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat}, +l2: U32, +t2: AT.Tree<U32>, +ps: List<&2, String>,
  +hok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool},
  +hpt: {B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts},
  +hrt: {NR.chars(SW.V(l2, t2)) == Norm.recs_text(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : String},
  +h10c: {FD.count(SW.V(l2, t2), 10) == List.length(&2, String, ps) : Nat},
  +hcr: {(DR.CRT(DR.TE(len, t, at, lf)) || Nat.is_eq(FD.count(SW.V(l2, t2), 13), 0n)) == True{} : Bool},
  +rp1: P.RunP, +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run}, +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool}))) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{B.Opts{st, w, True{}, o0, args}, Norm.MB{NR.tick(P.mkRun(rp))}, SPR0(len, t, lf, l2, t2, rest), P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}}):
  (hsp, r1) = sl
  (hn, r2) = r1
  (hle, hby) = r2
  +st0 = P.specRun(rp)
  +hib = Equal.trans(Bool, R.RunSt.inbody(st0), P.RunP.i(rp), True{}, LI.ib_spec(rp), hin)
  +hit = Equal.trans(Bool, R.RunSt.inbody(R.tick(st0)), R.RunSt.inbody(st0), True{}, ib_tick(st0), hib)
  +h10 = MW.lf_byte(len, t, d, hok, at, lf, hs, hfl, hlt)
  +hterm = TC.term_cr(len, t, d, hok, at, lf, hal, hlt, h10)
  +hl = {%Equal.sym(String, P.srctext(SPQ(l2, t2)), NR.chars(SW.V(l2, t2)), spq_txt(l2, t2)) : {B.Text.lines(_) == RS.LS(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : Ls()};
    RS.lines_ck(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf)), SW.V(l2, t2), hterm, hrt, h10c, hcr) : {B.Text.lines(P.srctext(SPQ(l2, t2))) == RS.LS(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : Ls()}}
  +hlf = {%Equal.sym(String, P.srctext(SPQ(l2, t2)), NR.chars(SW.V(l2, t2)), spq_txt(l2, t2)) : {S.ends_lf(_) == True{} : Bool};
    %Equal.sym(String, NR.chars(SW.V(l2, t2)), Norm.recs_text(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), hrt) : {S.ends_lf(_) == True{} : Bool};
    %Equal.sym(String, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), Bool.pick(String, DR.CRT(DR.TE(len, t, at, lf)), "\r\n", "\n"), hterm) : {S.ends_lf(Norm.recs_text(ps, _)) == True{} : Bool};
    lf_recs(ps, Bool.pick(String, DR.CRT(DR.TE(len, t, at, lf)), "\r\n", "\n"), tlf(DR.CRT(DR.TE(len, t, at, lf))), tne(DR.CRT(DR.TE(len, t, at, lf)))) : {S.ends_lf(P.srctext(SPQ(l2, t2))) == True{} : Bool}}
  went_inj(dfs, fa, T, cs, O, N, B.Opts{st, w, True{}, o0, args}, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, l2, t2, ps,
    hw, hr, hg, hsp, hn, hle, hal, hlt, hs, LP.inc_len(len, t, d, lf, hok, hlt), hx, hin, et, i1, s1, hpt, hl, hok2, hlf,
    rr_inj(rp, rp1, l2, t2, len, t, d, lf, rest, s1, hit))

def inj.tk(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat}, +l2: U32, +t2: AT.Tree<U32>, +ps: List<&2, String>,
  +hok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool},
  +hpt: {B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts},
  +hrt: {NR.chars(SW.V(l2, t2)) == Norm.recs_text(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : String},
  +h10c: {FD.count(SW.V(l2, t2), 10) == List.length(&2, String, ps) : Nat},
  +hcr: {(DR.CRT(DR.TE(len, t, at, lf)) || Nat.is_eq(FD.count(SW.V(l2, t2), 13), 0n)) == True{} : Bool},
  tk: WR.TKW(rp)) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{B.Opts{st, w, True{}, o0, args}, Norm.MB{NR.tick(P.mkRun(rp))}, SPR0(len, t, lf, l2, t2, rest), P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}}):
  (+rp1, q) = tk
  (et, q2) = q
  (i1, q3) = q2
  (s1, q4) = q3
  (n1, q5) = q4
  inj.tk2(dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, l2, t2, ps, hok2, hpt, hrt, h10c, hcr, rp1, et, i1, s1, LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt))


def inj.b(+b: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  q: DR.SPB(b, len, t, NS.split(C.BT(len, t), at, lf, o0, dfs), B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf)))) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  match b:
    case False{}:
      %Equal.sym(NS.Out, NS.split(C.BT(len, t), at, lf, o0, dfs), NS.Out{C.BT(len, t), None{}}, q) : S.AdvG(fa, T, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
        Norm.split.out(_, back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed))
      DE.dec(False{}, dfs, fa, T, cs, O, N, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig, {==})
    case True{}:
      (+l2, q1) = q
      (+t2, q2) = q1
      (+ps, q3) = q2
      (eo, q4) = q3
      (hok2, q5) = q4
      (hpt, q6) = q5
      (hrt, ck) = q6
      (h10c, hcr) = ck
      %Equal.sym(NS.Out, NS.split(C.BT(len, t), at, lf, o0, dfs), NS.Out{C.BT(len, t), Some{C.BT(l2, t2)}}, eo) : S.AdvG(fa, T, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
        Norm.split.out(_, back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed))
      +p = StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
      inj.tk(dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, l2, t2, ps, hok2, hpt, hrt, h10c, hcr,
        PR.run_tick(rp, W.c9_0(S.md_ok(S.MBP{rp}), W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)))

def inj.spr(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  r: DR.SPR(len, t, NS.split(C.BT(len, t), at, lf, o0, dfs), B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf)))) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, B.Opts{st, w, True{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  (+b, q) = r
  inj.b(b, dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, q)

# The byte mode, a byte source, in the body, with -m, multi's answer Some:
# the byte splitter (norm_split.bend's split) either gives the line back
# (the decoded path: the String splitter) or gives its records, put in front
# of the rest of the input.
def adv_split(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +esp: {R.Opts.split(o) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.split.b(back, o, P.mkRun(rp), C.BT(len, t), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      match sp:
        case False{}:
          Empty.absurd(S.AdvG(fa, T, cs, O, N, StM(dfs, B.Opts{st, w, False{}, o0, args}, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
            Norm.split.b(back, B.Opts{st, w, False{}, o0, args}, P.mkRun(rp), C.BT(len, t), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)), N.false_ne_true(esp))
        case True{}:
          inj.spr(dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, DR.split_t(len, t, d, hok, Nat.pow(2n, 32n), {==}, dfs, st, w, o0, args, at, lf, hal, hlt, MW.lf_byte(len, t, d, hok, at, lf, hs, hfl, hlt)))

# ---------------------------------------------------------------------------
# The same from a record buffer or a byte source (hold)
# ---------------------------------------------------------------------------

# A record of a split line has one ALT (the 9th test), so -m does not split
# it again.
def sp_abs(+dfs: B.Defs, +o: B.Opts, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +ps: List<&2, String>,
  +hrf: {S.recs_first(Con{P.SPP{len, t, d, at}, rest}) == True{} : Bool},
  +hpt: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool}))) ->
  Empty:
  (hsp, r1) = sl
  (hn, r2) = r1
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +S0 = P.srctext(P.SPP{len, t, d, at})
  +S1 = P.srctext(P.SPP{len, t, d, (lf + 1 : U32)})
  +hrt = W.and_l(S.rtok(S0), S.recs_first(rest), hrf)
  +ho = W.and_r(S.ends_lf(S0), S.all_one(B.Text.lines(S0)), hrt)
  +el = Equal.trans(List<&2, B.Line>, B.Text.lines(S0), B.Text.lines(String.append(A, String.append("\n", S1))), Con{l, B.Text.lines(S1)},
    Equal.cong(String, List<&2, B.Line>, x => B.Text.lines(x), S0, String.append(A, String.append("\n", S1)), hsp), LSS.lines_cons(A, S1, hn))
  +h1 = W.and_l(S.one_alt(l), S.all_one(B.Text.lines(S1)), {(%el : {S.all_one(_) == True{} : Bool}; ho) : {S.all_one(Con{l, B.Text.lines(S1)}) == True{} : Bool}})
  OI.one_not_pieces(dfs, o, B.Line.body(l), ps, h1, hpt)

def inj.b_sp(+b: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(True{}, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(True{}, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(True{}, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  q: DR.SPB(b, len, t, NS.split(C.BT(len, t), at, lf, o0, dfs), B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf))),
  +hnr: LI.HNE(True{}, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(True{}, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed)):
  match b:
    case False{}:
      %Equal.sym(NS.Out, NS.split(C.BT(len, t), at, lf, o0, dfs), NS.Out{C.BT(len, t), None{}}, q) : S.AdvG(fa, T, cs, O, N, LI.PPs(True{}, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
        Norm.split.out(_, back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed))
      DE.dec(True{}, dfs, fa, T, cs, O, N, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig, hnr)
    case True{}:
      (+l2, q1) = q
      (+t2, q2) = q1
      (+ps, q3) = q2
      (eo, q4) = q3
      (hok2, q5) = q4
      (hpt, q6) = q5
      +o = {B.Opts{st, w, True{}, o0, args} : B.Opts}
      +p = LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
      +h8 = W.c9_8(W.W0(fa, p), W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
      +AB = E.all_bytes(S.opts_args(o))
      +RF = S.recs_first(Con{P.SPP{len, t, d, at}, rest})
      +RR = S.recs_run(S.MBP{LI.RTP(True{}, rp)}, Con{P.SPP{len, t, d, at}, rest})
      +hrf = W.and_r(AB, RF, W.and_l(Bool.and(AB, RF), RR, h8))
      Empty.absurd(S.AdvG(fa, T, cs, O, N, p,
        Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, o, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed)),
        sp_abs(dfs, o, len, t, d, at, lf, rest, ps, hrf, hpt, LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt)))

def inj.b_h(+b: Bool, +hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  q: DR.SPB(b, len, t, NS.split(C.BT(len, t), at, lf, o0, dfs), B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf))),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match hold:
    case False{}:
      inj.b(b, dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, q)
    case True{}:
      inj.b_sp(b, dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, q, hnr)

def inj.spr_h(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  r: DR.SPR(len, t, NS.split(C.BT(len, t), at, lf, o0, dfs), B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf))),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, B.Opts{st, w, True{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, B.Opts{st, w, True{}, o0, args}, P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  (+b, q) = r
  inj.b_h(b, hold, dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, q, hnr)

def adv_split_h(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +esp: {R.Opts.split(o) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.split.b(back, o, P.mkRun(rp), C.BT(len, t), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      match sp:
        case False{}:
          Empty.absurd(S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, B.Opts{st, w, False{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
            Norm.split.b(back, B.Opts{st, w, False{}, o0, args}, P.mkRun(rp), C.BT(len, t), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)), N.false_ne_true(esp))
        case True{}:
          inj.spr_h(hold, dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, DR.split_t(len, t, d, hok, Nat.pow(2n, 32n), {==}, dfs, st, w, o0, args, at, lf, hal, hlt, MW.lf_byte(len, t, d, hok, at, lf, hs, hfl, hlt)), hnr)
