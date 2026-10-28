import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Q
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_fasteq.bend as FE
import ./proof_e_task_buf.bend as BUF
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/fast.bend as F
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N

# Phase E, area D (task): once Q is in the String mode it stays there:
# advance on a String-mode state gives a String-mode state, whatever it
# does. (A task that switched to the String mode ends dirty.)

def md_ms(md: Q.Md) -> Bool:
  match md:
    case Q.MB{r}:
      False{}
    case Q.MS{s, qs, ql, c}:
      True{}

def st_ms(st: Q.St) -> Bool:
  match st:
    case Q.St{o, md, src, pend, eof, back, win, asked, fneed}:
      md_ms(md)

def adv_ms(a: Q.Adv) -> Bool:
  match a:
    case Q.Went{st}:
      st_ms(st)
    case Q.Want{st, r}:
      st_ms(st)
    case Q.Idle{st}:
      st_ms(st)
    case Q.Ended{st}:
      st_ms(st)
    case Q.Yield{st}:
      st_ms(st)

def out_ms(+s: R.RunSt, +qs: List<&2, String>, +ql: Nat) -> {md_ms(Q.ms.out(s, qs, ql)) == True{} : Bool}:
  match s:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

def done_ms(+o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, cx: Q.Cx, win: Q.Win) ->
  {adv_ms(Q.ms.done(o, s, qs, ql, cx, win)) == True{} : Bool}:
  match cx:
    case Q.Cx{rest, pend, eof}:
      out_ms(s, qs, ql)

def want_ms(+o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +p: String, cx: Q.Cx, win: Q.Win, +reqs: List<&2, Pr.Req>, +back: Nat) ->
  {adv_ms(Q.ms.want(o, s, qs, ql, p, cx, win, reqs, back)) == True{} : Bool}:
  match cx:
    case Q.Cx{rest, pend, eof}:
      {==}

def body_ms(+o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +p: String, +l: B.Line, +fs: List<&2, String>, cx: Q.Cx, v: Q.Vd) ->
  {adv_ms(Q.ms.body(o, s, qs, ql, p, l, fs, cx, v)) == True{} : Bool}:
  match v:
    case Q.VRes{win, +r}:
      +s1 = R.tick(s)
      done_ms(o, R.body_line(r, s1, o, l, Q.at_of(R.RunSt.n(s1), fs), B.Rec.pos(fs)), qs, ql, cx, win)
    case Q.VSame{win}:
      +s1 = R.tick(s)
      done_ms(o, R.body_line(B.Res{B.Normalized{}, B.Rec.pos(fs), B.Line.body(l), False{}}, s1, o, l, Q.at_of(R.RunSt.n(s1), fs), B.Rec.pos(fs)), qs, ql, cx, win)
    case Q.VWant{win, +reqs, +back}:
      want_ms(o, s, qs, ql, p, cx, win, reqs, back)

def linek_ms(+inbody: Bool, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +p: String, +l: B.Line, +back: Nat, cx: Q.Cx, win: Q.Win) ->
  {adv_ms(Q.ms.line.k(inbody, o, s, qs, ql, p, l, back, cx, win)) == True{} : Bool}:
  match inbody:
    case False{}:
      done_ms(o, R.head_line(R.is_chrom_line(B.Line.body(l)), R.tick(s), o, l), qs, ql, cx, win)
    case True{}:
      +fs = J.pfs(B.Line.body(l))
      body_ms(o, s, qs, ql, p, l, fs, cx, Q.verdict(back, win, fs, B.Line.body(l)))

def line_ms(+o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +p: String, +back: Nat, cx: Q.Cx, win: Q.Win) ->
  {adv_ms(Q.ms.line(o, s, qs, ql, p, back, cx, win)) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +out, +ns, +x}:
      linek_ms(i, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}, qs, ql, p, Q.line(p), back, cx, win)

def sbif_ms(+part: Bool, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32,
  rest: List<&1, Q.Src>, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +fneed: Bool) ->
  {adv_ms(Q.ms.sb.if(part, o, s, qs, ql, C.BT(len, t), at, lf, rest, pend, eof, back, win, fneed)) == True{} : Bool}:
  match part:
    case True{}:
      {==}
    case False{}:
      +X = Q.chars(BUF.TY(len, t, at, (lf - at : U32)))
      %Equal.sym(D.Bytes & String, Q.text(C.BT(len, t), at, (lf - at : U32)), (C.BT(len, t), X), BUF.text_p(len, t, at, (lf - at : U32))) :
        {adv_ms(Q.ms.sb.k(o, s, qs, ql, at, lf, _, rest, pend, eof, back, win)) == True{} : Bool}
      line_ms(o, s, qs, ql, X, back, Q.Cx{Q.SB{C.BT(len, t), (lf + 1 : U32)} <> rest, pend, eof}, win)

def src_ms(+src: List<&2, P.SrcP>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win,
  +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) ->
  {adv_ms(Q.ms.src(P.mkSrcs(src), o, s, qs, ql, pend, eof, back, win, asked, fneed)) == True{} : Bool}:
  match src:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      +j = Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), at, len, 10))
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), at, len, 10), (C.BT(len, t), j), FE.find_pair(C.BT(len, t), at, len, 10)) :
        {adv_ms(Q.ms.sb(o, s, qs, ql, at, NF.lf.k(len, _), P.mkSrcs(rest), pend, eof, back, win, fneed)) == True{} : Bool}
      sbif_ms(U32.is_eq(j, len), o, s, qs, ql, len, t, at, j, P.mkSrcs(rest), pend, eof, back, win, fneed)
    case Con{P.SLP{+p}, +rest}:
      line_ms(o, s, qs, ql, p, back, Q.Cx{P.mkSrcs(rest), pend, eof}, win)

def full_ms(+full: Bool, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win,
  +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) ->
  {adv_ms(Q.ms.full(full, o, s, qs, ql, P.mkSrcs(src), pend, eof, back, win, asked, fneed)) == True{} : Bool}:
  match full:
    case True{}:
      {==}
    case False{}:
      src_ms(src, o, s, qs, ql, pend, eof, back, win, asked, fneed)

def adv.k(+halt: Bool, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +code: Maybe<&2, Nat>, +src: List<&2, P.SrcP>, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win,
  +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) ->
  {adv_ms(Q.ms.adv(halt, o, s, qs, ql, code, P.mkSrcs(src), pend, eof, back, win, asked, fneed)) == True{} : Bool}:
  match halt code:
    case _ Some{c}:
      {==}
    case True{} None{}:
      {==}
    case False{} None{}:
      full_ms(Nat.is_le(Q.lim(), ql), o, s, qs, ql, src, pend, eof, back, win, asked, fneed)

def md_ms_p(+m: S.MdP) -> Bool:
  match m:
    case S.MBP{rp}:
      False{}
    case S.MSP{s, qs, ql, c}:
      True{}

# advance keeps the String mode.
def ms_stays(+fa: List<&2, B.Contig>, +p: S.StP,
  +h: {md_ms_p(S.StP.md(p)) == True{} : Bool}) ->
  {adv_ms(Q.advance(S.mkSt(fa, p))) == True{} : Bool}:
  match p:
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      adv.k(R.RunSt.halt(s), o, s, qs, ql, code, src, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      Empty.absurd({adv_ms(Q.advance(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}))) == True{} : Bool}, N.false_ne_true(h))

# A pictured state is in the String mode exactly when its picture is.
def st_ms_p(+fa: List<&2, B.Contig>, +p: S.StP) -> {st_ms(S.mkSt(fa, p)) == md_ms_p(S.StP.md(p)) : Bool}:
  match p:
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}
