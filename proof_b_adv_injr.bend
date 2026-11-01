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
import ./proof_b_frame.bend as FR
import ./proof_b_frame_fr.bend as FF
import ./proof_b_lines_str.bend as LSS
import ./proof_b_adv_line.bend as LI
import ./proof_s_recs.bend as RS
import ./proof_s_inj.bend as INJ
import ./proof_s_one.bend as OI
import ./proof_s_chars.bend as CH
import ./proof_b_adv_str.bend as T
import ./proof_b_adv_wf.bend as W
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C

# The String path's branch of a split line in the byte mode (norm_seq.bend's
# inject.r): the records of a line split on its text go in front of the rest
# of the input as exact lines (SR sources), with the run ticked for the line;
# handled one by one later, they give what the spec gives the line. As the
# byte splitter's branch (proof_b_adv_split.bend), with SRP sources. Every
# variable is reusable.

def Ls() -> Data:
  List<&2, B.Line>

def Srcs() -> Data:
  List<&2, P.SrcP>

def StM(+dfs: B.Defs, +o: B.Opts, +md: S.MdP, +src: Srcs(), +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}

def SB(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32) -> P.SrcP:
  P.SBP{len, t, d, at}

# The records of a split line, as SR sources, before x.
def srps(ps: List<&2, String>, +term: String, x: Srcs()) -> Srcs():
  match ps:
    case Nil{}:
      x
    case +p <> t:
      Con{P.SRP{B.Line{p, term}}, srps(t, term, x)}

law plain_srps:
  for +ps: List<&2, String>
  for +term: String
  for +x: Srcs()
  {S.plain(srps(ps, term, x)) == S.plain(x) : Srcs()}

def plain_srps(ps, term, x):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      plain_srps(t, term, x)

law recs_srps:
  for +ps: List<&2, String>
  for +term: String
  for +x: Srcs()
  {S.recs(srps(ps, term, x)) == srps(ps, term, S.recs(x)) : Srcs()}

def recs_srps(ps, term, x):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      Equal.cong(Srcs(), Srcs(), z => Con{P.SRP{B.Line{p, term}}, z}, S.recs(srps(t, term, x)), srps(t, term, S.recs(x)), recs_srps(t, term, x))

law rg_srps:
  for +ps: List<&2, String>
  for +term: String
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  {S.RG(srps(ps, term, Nil{}), fa, dfs, o, st) == S.rgo(RS.LS(ps, term), fa, dfs, o, st) : R.RunSt}

def rg_srps(ps, term, fa, dfs, o, st):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      rg_srps(t, term, fa, dfs, o, S.rstep(fa, dfs, o, st, B.Line{p, term}))

law msrc_srps:
  for +ps: List<&2, String>
  for +term: String
  for +x: Srcs()
  {S.msrc(srps(ps, term, x)) == S.msrc(x) : Nat}

def msrc_srps(ps, term, x):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      msrc_srps(t, term, x)

law mk_srps:
  for +ps: List<&2, String>
  for +term: String
  for +x: Srcs()
  {P.mkSrcs(srps(ps, term, x)) == Norm.recs_src(ps, term, P.mkSrcs(x)) : List<&1, Norm.Src>}

def mk_srps(ps, term, x):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      Equal.cong(List<&1, Norm.Src>, List<&1, Norm.Src>, z => Con{Norm.SR{B.Line{p, term}}, z}, P.mkSrcs(srps(t, term, x)), Norm.recs_src(t, term, P.mkSrcs(x)), mk_srps(t, term, x))

# Texts ending with LF
# ===================

def lf_ne(+y: String, +hy: {S.ends_lf(y) == True{} : Bool}, +hne: {String.is_empty(y) == False{} : Bool}) -> {T.ends_nl(y) == True{} : Bool}:
  +OR = Bool.or(String.is_empty(y), T.ends_nl(y))
  +h2 = Equal.trans(Bool, OR, S.ends_lf(y), True{}, Equal.sym(Bool, S.ends_lf(y), OR, T.lf_eq(y)), hy)
  Equal.trans(Bool, T.ends_nl(y), OR, True{},
    {%Equal.sym(Bool, String.is_empty(y), False{}, hne) : {T.ends_nl(y) == Bool.or(_, T.ends_nl(y)) : Bool}; {==} : {T.ends_nl(y) == OR : Bool}}, h2)

def lf_pre(+x: String, +y: String, +hy: {S.ends_lf(y) == True{} : Bool}, +hne: {String.is_empty(y) == False{} : Bool}) ->
  {S.ends_lf(String.append(x, y)) == True{} : Bool}:
  %Equal.sym(Bool, S.ends_lf(String.append(x, y)), Bool.or(String.is_empty(String.append(x, y)), T.ends_nl(String.append(x, y))), T.lf_eq(String.append(x, y))) : {_ == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(String.append(x, y)), False{}, T.app_ne(x, y, hne)) : {Bool.or(_, T.ends_nl(String.append(x, y))) == True{} : Bool}
  %Equal.sym(Bool, T.ends_nl(String.append(x, y)), T.ends_nl(y), T.nl_app(x, y, hne)) : {Bool.or(False{}, _) == True{} : Bool}
  lf_ne(y, hy, hne)

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

# The sources' text, records first, ends with LF when the rest's does.
law lf_srps:
  for +ps: List<&2, String>
  for +term: String
  for +x: Srcs()
  for +ht: {S.ends_lf(term) == True{} : Bool}
  for +hne: {String.is_empty(term) == False{} : Bool}
  for +hx: {S.ends_lf(P.srcstext(x)) == True{} : Bool}
  {S.ends_lf(P.srcstext(srps(ps, term, x))) == True{} : Bool}

def lf_srps(ps, term, x, ht, hne, hx):
  match ps:
    case Nil{}:
      hx
    case +p <> +t:
      lf_app(String.append(p, term), P.srcstext(srps(t, term, x)), lf_pre(p, term, ht, hne), lf_srps(t, term, x, ht, hne, hx))

# A line's terminator: LF or CR LF.
def tm.k(cr: Bool, +A: String) ->
  {Bool.and(Bool.and(S.ends_lf(B.Line.term(B.Text.line.if(cr, A))), Bool.not(String.is_empty(B.Line.term(B.Text.line.if(cr, A))))), E.is_bytes(B.Line.term(B.Text.line.if(cr, A)))) == True{} : Bool}:
  match cr:
    case True{}:
      {==}
    case False{}:
      {==}

law term_ok:
  for +A: String
  {Bool.and(Bool.and(S.ends_lf(B.Line.term(B.Text.line(A))), Bool.not(String.is_empty(B.Line.term(B.Text.line(A))))), E.is_bytes(B.Line.term(B.Text.line(A)))) == True{} : Bool}

def term_ok(A):
  tm.k(String.ends_with(A, "\r"), A)

def not_t(x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, W.ft(h))
    case False{}:
      {==}

# Bytes
# =====

law byt_bytes:
  for +s: String
  for +h: {CH.ALLC(CH.Byt{}, s) == True{} : Bool}
  {E.is_bytes(s) == True{} : Bool}

def byt_bytes(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      W.and_tt(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), W.and_l(U32.is_lt(Char.to_u32(c), 256), CH.ALLC(CH.Byt{}, t), h),
        byt_bytes(t, W.and_r(U32.is_lt(Char.to_u32(c), 256), CH.ALLC(CH.Byt{}, t), h)))

law bytes_byt:
  for +s: String
  for +h: {E.is_bytes(s) == True{} : Bool}
  {CH.ALLC(CH.Byt{}, s) == True{} : Bool}

def bytes_byt(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      W.and_tt(U32.is_lt(Char.to_u32(c), 256), CH.ALLC(CH.Byt{}, t), W.and_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), h),
        bytes_byt(t, W.and_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), h)))

# The sources: each record bytes, its text ending with LF, then x.
def so.k(+p: String, t: List<&2, String>, +term: String, +sp0: P.SrcP, +r0: Srcs(),
  +hp: {E.is_bytes(String.append(p, term)) == True{} : Bool},
  +hl: {S.ends_lf(String.append(p, term)) == True{} : Bool},
  ih: {S.srcs_ok(srps(t, term, Con{sp0, r0})) == True{} : Bool}) ->
  {S.srcs_ok(Con{P.SRP{B.Line{p, term}}, srps(t, term, Con{sp0, r0})}) == True{} : Bool}:
  match t:
    case Nil{}:
      W.and_tt(Bool.and(E.is_bytes(String.append(p, term)), S.ends_lf(String.append(p, term))), S.srcs_ok(Con{sp0, r0}), W.and_tt(E.is_bytes(String.append(p, term)), S.ends_lf(String.append(p, term)), hp, hl), ih)
    case Con{+p2, +t2}:
      W.and_tt(Bool.and(E.is_bytes(String.append(p, term)), S.ends_lf(String.append(p, term))), S.srcs_ok(srps(Con{p2, t2}, term, Con{sp0, r0})), W.and_tt(E.is_bytes(String.append(p, term)), S.ends_lf(String.append(p, term)), hp, hl), ih)

law srcs_srps:
  for +ps: List<&2, String>
  for +term: String
  for +sp0: P.SrcP
  for +r0: Srcs()
  for +hb: {CH.ALLS(CH.Byt{}, ps) == True{} : Bool}
  for +htm: {Bool.and(Bool.and(S.ends_lf(term), Bool.not(String.is_empty(term))), E.is_bytes(term)) == True{} : Bool}
  for +hx: {S.srcs_ok(Con{sp0, r0}) == True{} : Bool}
  {S.srcs_ok(srps(ps, term, Con{sp0, r0})) == True{} : Bool}

def srcs_srps(ps, term, sp0, r0, hb, htm, hx):
  match ps:
    case Nil{}:
      hx
    case +p <> +t:
      +h12 = W.and_l(Bool.and(S.ends_lf(term), Bool.not(String.is_empty(term))), E.is_bytes(term), htm)
      +hlf = W.and_l(S.ends_lf(term), Bool.not(String.is_empty(term)), h12)
      +hne = not_t(String.is_empty(term), W.and_r(S.ends_lf(term), Bool.not(String.is_empty(term)), h12))
      +hbt = W.and_r(Bool.and(S.ends_lf(term), Bool.not(String.is_empty(term))), E.is_bytes(term), htm)
      +hbp = byt_bytes(p, W.and_l(CH.ALLC(CH.Byt{}, p), CH.ALLS(CH.Byt{}, t), hb))
      so.k(p, t, term, sp0, r0, LSS.bytes_app(p, term, hbp, hbt), lf_pre(p, term, hlf, hne),
        srcs_srps(t, term, sp0, r0, W.and_r(CH.ALLC(CH.Byt{}, p), CH.ALLS(CH.Byt{}, t), hb), htm, hx))

# The records come first, each with one ALT.
law rf_srps:
  for +ps: List<&2, String>
  for +term: String
  for +x: Srcs()
  for +h1: {S.all_one(RS.LS(ps, term)) == True{} : Bool}
  for +h2: {S.recs_first(x) == True{} : Bool}
  {S.recs_first(srps(ps, term, x)) == True{} : Bool}

def rf_srps(ps, term, x, h1, h2):
  match ps:
    case Nil{}:
      h2
    case +p <> +t:
      W.and_tt(S.one_alt(B.Line{p, term}), S.recs_first(srps(t, term, x)), W.and_l(S.one_alt(B.Line{p, term}), S.all_one(RS.LS(t, term)), h1),
        rf_srps(t, term, x, W.and_r(S.one_alt(B.Line{p, term}), S.all_one(RS.LS(t, term)), h1), h2))

def or_tr(x: Bool, +y: Bool, +h: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

def n_tick(+s0: R.RunSt) -> {R.RunSt.n(R.tick(s0)) == 1n+R.RunSt.n(s0) : Nat}:
  match s0:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

def ib_tick(+st: R.RunSt) -> {R.RunSt.inbody(R.tick(st)) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

# While the records wait, the run is in the body and has counted their line.
def rr_injr(+rp: P.RunP, +rp1: P.RunP, +src: Srcs(),
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +hit: {R.RunSt.inbody(R.tick(P.specRun(rp))) == True{} : Bool}) ->
  {S.recs_run(S.MBP{rp1}, src) == True{} : Bool}:
  +st0 = P.specRun(rp)
  or_tr(List.is_empty(&2, P.SrcP, S.recs(src)), Bool.and(R.RunSt.inbody(P.specRun(rp1)), Nat.is_le(1n, R.RunSt.n(P.specRun(rp1)))),
    {(%Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st0), s1) : {Bool.and(R.RunSt.inbody(_), Nat.is_le(1n, R.RunSt.n(_))) == True{} : Bool};
      %Equal.sym(Bool, R.RunSt.inbody(R.tick(st0)), True{}, hit) : {Bool.and(_, Nat.is_le(1n, R.RunSt.n(R.tick(st0)))) == True{} : Bool};
      %Equal.sym(Nat, R.RunSt.n(R.tick(st0)), 1n+R.RunSt.n(st0), n_tick(st0)) : {Bool.and(True{}, Nat.is_le(1n, _)) == True{} : Bool};
      N.le_zero_l(R.RunSt.n(st0))) : {Bool.and(R.RunSt.inbody(P.specRun(rp1)), Nat.is_le(1n, R.RunSt.n(P.specRun(rp1)))) == True{} : Bool}})

# The state after
# ===============

def QR(+dfs: B.Defs, +o: B.Opts, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +lf: U32, +ps: List<&2, String>, +term: String,
  +rest: Srcs(), +pd: P.PdP, +eof: Bool, +wp: PC.WP) -> S.StP:
  StM(dfs, o, S.MBP{rp1}, srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest}), pd, eof, 0n, wp, None{}, False{})

# Its text still to come is that of the input after the line.
law itq:
  for +dfs: B.Defs
  for +o: B.Opts
  for +rp1: P.RunP
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +lf: U32
  for +ps: List<&2, String>
  for +term: String
  for +rest: Srcs()
  for +pd: P.PdP
  for +eof: Bool
  for +wp: PC.WP
  for +cs: List<&2, String>
  {S.intext(QR(dfs, o, rp1, len, t, d, lf, ps, term, rest, pd, eof, wp), cs) == S.intext(StM(dfs, o, S.MBP{rp1}, Con{SB(len, t, d, (lf + 1 : U32)), rest}, pd, eof, 0n, wp, None{}, False{}), cs) : String}

def itq(dfs, o, rp1, len, t, d, lf, ps, term, rest, pd, eof, wp, cs):
  %Equal.sym(Srcs(), S.plain(srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest})), S.plain(Con{SB(len, t, d, (lf + 1 : U32)), rest}),
    plain_srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest})) :
    {String.append(P.srcstext(_), String.append(P.pdtext(pd), S.concat_if(eof, cs))) == S.intext(StM(dfs, o, S.MBP{rp1}, Con{SB(len, t, d, (lf + 1 : U32)), rest}, pd, eof, 0n, wp, None{}, False{}), cs) : String}
  {==}

# After the end of the file: the sources' text still ends with LF.
def eof_lf(eof: Bool, +pd: P.PdP, +y: String, +y2: String,
  f: {S.ends_lf(y) == True{} : Bool} -> {S.ends_lf(y2) == True{} : Bool},
  +h: {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(y))) == True{} : Bool}) ->
  {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(y2))) == True{} : Bool}:
  match eof:
    case False{}:
      {==}
    case True{}:
      W.and_tt(String.is_empty(P.pdtext(pd)), S.ends_lf(y2), W.and_l(String.is_empty(P.pdtext(pd)), S.ends_lf(y), h),
        f(W.and_r(String.is_empty(P.pdtext(pd)), S.ends_lf(y), h)))

def wf_injr(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +rest: Srcs(), +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +ps: List<&2, String>, +term: String,
  +hw: {S.WF(fa, StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hs: LI.SPLIT(len, t, d, at, lf), +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +i1: {S.md_ok(S.MBP{rp1}) == True{} : Bool},
  +hb: {CH.ALLS(CH.Byt{}, ps) == True{} : Bool},
  +htm: {Bool.and(Bool.and(S.ends_lf(term), Bool.not(String.is_empty(term))), E.is_bytes(term)) == True{} : Bool},
  +hone: {S.all_one(RS.LS(ps, term)) == True{} : Bool},
  +hrr: {S.recs_run(S.MBP{rp1}, srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest})) == True{} : Bool}) ->
  {S.WF(fa, QR(dfs, o, rp1, len, t, d, lf, ps, term, rest, pd, eof, wp)) == True{} : Bool}:
  +p = StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)
  +q = QR(dfs, o, rp1, len, t, d, lf, ps, term, rest, pd, eof, wp)
  +src2 = srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest})
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
  +hab = W.and_l(Bool.and(AB, NR0), S.recs_run(S.MBP{rp}, Con{SB(len, t, d, at), rest}), h8)
  +h12 = W.and_l(Bool.and(S.ends_lf(term), Bool.not(String.is_empty(term))), E.is_bytes(term), htm)
  +hlf = W.and_l(S.ends_lf(term), Bool.not(String.is_empty(term)), h12)
  +hne = not_t(String.is_empty(term), W.and_r(S.ends_lf(term), Bool.not(String.is_empty(term)), h12))
  +hpd = W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +w5p = LI.eof_next(eof, rest, pd, len, t, d, at, lf, hs, W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw))
  +w5 = eof_lf(eof, pd, P.srcstext(Con{SB(len, t, d, (lf + 1 : U32)), rest}), P.srcstext(src2),
    hx => lf_srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest}, hlf, hne, hx), w5p)
  +b8 = W.and_tt(Bool.and(AB, S.recs_first(src2)), S.recs_run(S.MBP{rp1}, src2),
    W.and_tt(AB, S.recs_first(src2), W.and_l(AB, NR0, hab), rf_srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest}, hone, W.and_r(AB, NR0, hab))), hrr)
  W.c9_mk(S.md_ok(S.MBP{rp1}), W.W1(fa, q), a2, a3, W.W4(fa, q), W.W5(fa, q), a6, a7, W.W8(fa, q), i1,
    srcs_srps(ps, term, SB(len, t, d, (lf + 1 : U32)), rest, hb, htm, LI.srcs_next(rest, len, t, d, at, lf, hs, hle, W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw))),
    W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw),
    or_tr(S.src_empty(src2), String.is_empty(P.pdtext(pd)), hpd),
    w5, W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), b8)

# The report and what moved
# =========================

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


def SPLITX(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32) -> Type:
  LI.SPLIT(len, t, d, at, lf)

# The report: the records, one by one from the ticked run, stand for the
# line they came from.
def rep_injr(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: Srcs(), +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +ps: List<&2, String>,
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +hp: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts}) ->
  {S.report(fa, cs, O, N, QR(dfs, o, rp1, len, t, d, lf, ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), rest, pd, eof, wp)) == T : R.Report}:
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +tm = B.Line.term(l)
  +p = StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)
  +q = QR(dfs, o, rp1, len, t, d, lf, ps, tm, rest, pd, eof, wp)
  +q0 = StM(dfs, o, S.MBP{rp1}, Con{SB(len, t, d, (lf + 1 : U32)), rest}, pd, eof, 0n, wp, None{}, False{})
  +src2 = srps(ps, tm, Con{SB(len, t, d, (lf + 1 : U32)), rest})
  +IT2 = S.intext(q0, cs)
  +LS2 = B.Text.lines(IT2)
  +LSP = B.Text.lines(S.intext(p, cs))
  +st = P.specRun(rp)
  +hib = Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, LI.ib_spec(rp), hin)
  +hit = Equal.trans(Bool, R.RunSt.inbody(R.tick(st)), R.RunSt.inbody(st), True{}, ib_tick(st), hib)
  +hxt = Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, LI.halt_spec(rp), hx)
  %Equal.sym(String, S.intext(q, cs), IT2, itq(dfs, o, rp1, len, t, d, lf, ps, tm, rest, pd, eof, wp, cs)) :
    {R.finish(L.run.go(B.Text.lines(_), fa, L.defs.go(B.Text.lines(_), R.RunSt.inbody(P.specRun(rp1)), dfs), o, S.RG(S.recs(src2), fa, L.defs.go(B.Text.lines(_), R.RunSt.inbody(P.specRun(rp1)), dfs), o, S.pre(O, N, P.specRun(rp1))))) == T : R.Report}
  %Equal.sym(Srcs(), S.recs(src2), srps(ps, tm, Nil{}), recs_srps(ps, tm, Con{SB(len, t, d, (lf + 1 : U32)), rest})) :
    {R.finish(L.run.go(LS2, fa, L.defs.go(LS2, R.RunSt.inbody(P.specRun(rp1)), dfs), o, S.RG(_, fa, L.defs.go(LS2, R.RunSt.inbody(P.specRun(rp1)), dfs), o, S.pre(O, N, P.specRun(rp1))))) == T : R.Report}
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st), s1) :
    {R.finish(L.run.go(LS2, fa, L.defs.go(LS2, R.RunSt.inbody(_), dfs), o, S.RG(srps(ps, tm, Nil{}), fa, L.defs.go(LS2, R.RunSt.inbody(_), dfs), o, S.pre(O, N, _)))) == T : R.Report}
  %Equal.sym(Bool, R.RunSt.inbody(R.tick(st)), True{}, hit) :
    {R.finish(L.run.go(LS2, fa, L.defs.go(LS2, _, dfs), o, S.RG(srps(ps, tm, Nil{}), fa, L.defs.go(LS2, _, dfs), o, S.pre(O, N, R.tick(st))))) == T : R.Report}
  %Equal.sym(B.Defs, L.defs.go(LS2, True{}, dfs), dfs, FF.defs_done(LS2, dfs)) :
    {R.finish(L.run.go(LS2, fa, _, o, S.RG(srps(ps, tm, Nil{}), fa, _, o, S.pre(O, N, R.tick(st))))) == T : R.Report}
  %Equal.sym(R.RunSt, S.RG(srps(ps, tm, Nil{}), fa, dfs, o, S.pre(O, N, R.tick(st))), S.rgo(RS.LS(ps, tm), fa, dfs, o, S.pre(O, N, R.tick(st))), rg_srps(ps, tm, fa, dfs, o, S.pre(O, N, R.tick(st)))) :
    {R.finish(L.run.go(LS2, fa, dfs, o, _)) == T : R.Report}
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

# Both states' definitions are the run's: the text after them is the body.
def defs_ib(+ls: List<&2, B.Line>, +dfs: B.Defs, +i: Bool, +hi: {i == True{} : Bool}) -> {L.defs.go(ls, i, dfs) == dfs : B.Defs}:
  %Equal.sym(Bool, i, True{}, hi) : {L.defs.go(ls, _, dfs) == dfs : B.Defs}
  FF.defs_done(ls, dfs)

def defs_in2(+a: B.Defs, +b: B.Defs, +c: B.Defs, +ha: {a == c : B.Defs}, +hb: {b == c : B.Defs}) -> {a == b : B.Defs}:
  Equal.trans(B.Defs, a, c, b, ha, Equal.sym(B.Defs, b, c, hb))

def moved_injr(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: Srcs(), +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +ps: List<&2, String>,
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +hp: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts}) ->
  S.Moved(fa, cs, StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed), QR(dfs, o, rp1, len, t, d, lf, ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), rest, pd, eof, wp)):
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +tm = B.Line.term(l)
  +p = StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)
  +q = QR(dfs, o, rp1, len, t, d, lf, ps, tm, rest, pd, eof, wp)
  +q0 = StM(dfs, o, S.MBP{rp1}, Con{SB(len, t, d, (lf + 1 : U32)), rest}, pd, eof, 0n, wp, None{}, False{})
  +src2 = srps(ps, tm, Con{SB(len, t, d, (lf + 1 : U32)), rest})
  +IT2 = S.intext(q0, cs)
  +LSP = B.Text.lines(S.intext(p, cs))
  +st = P.specRun(rp)
  +hib = Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, LI.ib_spec(rp), hin)
  +hxt = Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, LI.halt_spec(rp), hx)
  +eD = Equal.trans(B.Defs, L.defs.go(LSP, R.RunSt.inbody(st), dfs), L.defs.go(LSP, True{}, dfs), dfs, Equal.cong(Bool, B.Defs, z => L.defs.go(LSP, z, dfs), R.RunSt.inbody(st), True{}, hib), FF.defs_done(LSP, dfs))
  +eit = itq(dfs, o, rp1, len, t, d, lf, ps, tm, rest, pd, eof, wp, cs)
  (Con{l, Nil{}},
    ({(%Equal.sym(String, S.intext(q, cs), IT2, eit) : {LSP == List.append(&2, B.Line, Con{l, Nil{}}, B.Text.lines(_)) : Ls()};
       Equal.trans(Ls(), LSP, B.Text.lines(String.append(A, String.append("\n", IT2))), Con{l, B.Text.lines(IT2)},
        Equal.cong(String, Ls(), x => B.Text.lines(x), S.intext(p, cs), String.append(A, String.append("\n", IT2)),
          Equal.sym(String, String.append(A, String.append("\n", IT2)), S.intext(p, cs),
            LI.itx(dfs, o, S.MBP{rp}, S.MBP{rp1}, rest, pd, eof, back, 0n, wp, asked, None{}, fneed, False{}, cs, len, t, d, at, lf, hs))),
        LSS.lines_cons(A, IT2, hn))) : {LSP == List.append(&2, B.Line, Con{l, Nil{}}, B.Text.lines(S.intext(q, cs))) : Ls()}},
    {%Equal.sym(B.Defs, L.defs.go(LSP, R.RunSt.inbody(st), dfs), dfs, eD) :
       {P.settle(S.RG(S.recs(src2), fa, _, o, P.specRun(rp1))) == P.settle(L.line_step(fa, _, o, st, l)) : R.RunSt};
     %Equal.sym(Srcs(), S.recs(src2), srps(ps, tm, Nil{}), recs_srps(ps, tm, Con{SB(len, t, d, (lf + 1 : U32)), rest})) :
       {P.settle(S.RG(_, fa, dfs, o, P.specRun(rp1))) == P.settle(L.line_step(fa, dfs, o, st, l)) : R.RunSt};
     %Equal.sym(R.RunSt, S.RG(srps(ps, tm, Nil{}), fa, dfs, o, P.specRun(rp1)), S.rgo(RS.LS(ps, tm), fa, dfs, o, P.specRun(rp1)), rg_srps(ps, tm, fa, dfs, o, P.specRun(rp1))) :
       {P.settle(_) == P.settle(L.line_step(fa, dfs, o, st, l)) : R.RunSt};
     %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st), s1) :
       {P.settle(S.rgo(RS.LS(ps, tm), fa, dfs, o, _)) == P.settle(L.line_step(fa, dfs, o, st, l)) : R.RunSt};
     %Equal.sym(R.RunSt, S.rgo(RS.LS(ps, tm), fa, dfs, o, R.tick(st)), L.line_step(fa, dfs, o, st, l), INJ.rgo_line(fa, dfs, dfs, o, st, l, ps, hxt, hib, hp)) :
       {P.settle(_) == P.settle(L.line_step(fa, dfs, o, st, l)) : R.RunSt};
     {==} : {P.settle(S.RG(S.recs(S.StP.src(q)), fa, S.DEFS(p, cs), o, P.specRun(rp1))) == P.settle(L.run.go(Con{l, Nil{}}, fa, S.DEFS(p, cs), o, S.RG(S.recs(S.StP.src(p)), fa, S.DEFS(p, cs), o, P.specRun(rp)))) : R.RunSt}},
    defs_in2(S.DEFS(q, cs), S.DEFS(p, cs), dfs,
      defs_ib(B.Text.lines(S.intext(q, cs)), dfs, R.RunSt.inbody(P.specRun(rp1)),
        Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp1)), R.RunSt.inbody(R.tick(st)), True{}, Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.specRun(rp1), R.tick(st), s1),
          Equal.trans(Bool, R.RunSt.inbody(R.tick(st)), R.RunSt.inbody(st), True{}, ib_tick(st), hib))),
      eD)))

def meas_injr(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: Srcs(), +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +ps: List<&2, String>, +term: String,
  +hm: {Nat.is_lt(S.measure(LI.P2(False{}, dfs, o, rp1, len, t, d, lf, rest, pd, eof, wp)), S.measure(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed))) == True{} : Bool}) ->
  {Nat.is_lt(S.measure(QR(dfs, o, rp1, len, t, d, lf, ps, term, rest, pd, eof, wp)), S.measure(StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed))) == True{} : Bool}:
  %Equal.sym(Nat, S.msrc(srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest})), S.msrc(Con{SB(len, t, d, (lf + 1 : U32)), rest}), msrc_srps(ps, term, Con{SB(len, t, d, (lf + 1 : U32)), rest})) :
    {Nat.is_lt(Nat.add(_, 1n), S.measure(StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed))) == True{} : Bool}
  hm

# A split line's records put in front of the input, as exact lines (SR).
law went_injr:
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
  for +rest: Srcs()
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +ps: List<&2, String>
  for +hw: {S.WF(fa, StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report}
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
  for +hbb: {E.is_bytes(B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == True{} : Bool}
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{NR.tick(P.mkRun(rp))}, Norm.recs_src(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), Con{Norm.SB{C.BT(len, t), (lf + 1 : U32)}, P.mkSrcs(rest)}),
      P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}})

def went_injr(dfs, fa, T, cs, O, N, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, ps, hw, hr, hs, hn, hle, hal, hlt, hat, hinc, hx, hin, et, i1, s1, hp, hbb):
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +tm = B.Line.term(l)
  +bd = B.Line.body(l)
  +p = StM(dfs, o, S.MBP{rp}, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)
  +q = QR(dfs, o, rp1, len, t, d, lf, ps, tm, rest, pd, eof, wp)
  +src2 = srps(ps, tm, Con{SB(len, t, d, (lf + 1 : U32)), rest})
  +st = P.specRun(rp)
  +hib = Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, LI.ib_spec(rp), hin)
  +hit = Equal.trans(Bool, R.RunSt.inbody(R.tick(st)), R.RunSt.inbody(st), True{}, ib_tick(st), hib)
  +hg1 = {%Equal.sym(R.RunSt, P.specRun(rp1), R.tick(st), s1) : {Bool.or(R.RunSt.inbody(_), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
    %Equal.sym(Bool, R.RunSt.inbody(R.tick(st)), True{}, hit) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
    {==} : {S.guard(O, N, q) == True{} : Bool}}
  +hb = CH.parts_chars(CH.Byt{}, dfs, o, bd, ps, hp, bytes_byt(bd, hbb), {==}, {==})
  +hone = OI.pieces_one(dfs, o, bd, ps, tm, hp)
  +hm = meas_injr(dfs, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, ps, tm,
    LI.meas_line(dfs, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hal, hlt, hle, hat, hinc))
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    S.AdvG(fa, T, cs, O, N, p, Norm.Went{Norm.St{o, Norm.MB{_}, Norm.recs_src(ps, tm, Con{Norm.SB{C.BT(len, t), (lf + 1 : U32)}, P.mkSrcs(rest)}), P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}})
  %mk_srps(ps, tm, Con{SB(len, t, d, (lf + 1 : U32)), rest}) :
    S.AdvG(fa, T, cs, O, N, p, Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp1)}, _, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}})
  (q, ({==}, (wf_injr(dfs, fa, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, ps, tm, hw, hs, hle, i1, hb, term_ok(A), hone,
      rr_injr(rp, rp1, src2, s1, hit)),
    (rep_injr(dfs, fa, T, cs, O, N, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, ps, hr, hs, hn, hx, hin, s1, hp),
    (W.less_lt(q, p, hm),
    ({==}, ({==}, (hg1, ({==},
    (moved_injr(dfs, fa, cs, o, rp, rp1, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, ps, hs, hn, hx, hin, s1, hp),
     hk => ((lf + 1 : U32), plain_srps(ps, tm, Con{SB(len, t, d, (lf + 1 : U32)), rest}))))))))))))

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

