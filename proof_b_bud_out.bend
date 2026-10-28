import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_ho.bend as HO
import ./proof_b_budget_dig.bend as G
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_finms.bend as DF
import ./proof_b_run.bend as PR
import ./proof_b_run_lem.bend as LM
import ./proof_b_enc.bend as ENC
import ./proof_b_lit.bend as LIT
import ./proof_base.bend as PB
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# The budget at the end of a step (notes/bytes_proofs_budget.md, "For
# pb-run", R3 and R4). out keeps everything WA and bi read (the sources,
# line end, eof, back, window, asked, fneed and the mode) and the next; the
# end of the run says Finish (no reads), or, in the String mode with more
# than 2^30 bytes left, hands out 2^30 of them and asks for another step.

# ---------------------------------------------------------------------------
# out
# ---------------------------------------------------------------------------

# A state with the run m and the rest pictured.
def OSt(+o: B.Opts, m: Norm.Md, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> Norm.St:
  Norm.St{o, m, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed}

# The mode md.take leaves.
def tmd(q: (D.Bytes & List<&2, B.Note>) & Norm.Md) -> Norm.Md:
  match q:
    case (on, md):
      md

def ok_st(q: (D.Bytes & List<&2, B.Note>) & Norm.Md, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +nx: Pr.Next) ->
  {BN.sst(Norm.out.k(q, o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx)) == OSt(o, tmd(q), src, pd, eof, back, fa, wp, asked, fneed) : Norm.St}:
  match q:
    case ((b, ns), md):
      {==}

def ok_nx(q: (D.Bytes & List<&2, B.Note>) & Norm.Md, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +nx: Pr.Next) ->
  {BN.snx(Norm.out.k(q, o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx)) == nx : Pr.Next}:
  match q:
    case ((b, ns), md):
      {==}

# out's state: the one it ends, with the mode take leaves.
def o_st(m: Norm.Md, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +nx: Pr.Next) ->
  {BN.sst(Norm.out(OSt(o, m, src, pd, eof, back, fa, wp, asked, fneed), nx)) == OSt(o, tmd(Norm.md.take(m, DO.lsum(src))), src, pd, eof, back, fa, wp, asked, fneed) : Norm.St}:
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
    {BN.sst(Norm.out.left(o, m, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx)) == OSt(o, tmd(Norm.md.take(m, DO.lsum(src))), src, pd, eof, back, fa, wp, asked, fneed) : Norm.St}
  ok_st(Norm.md.take(m, DO.lsum(src)), o, src, pd, eof, back, fa, wp, asked, fneed, nx)

def o_nx(m: Norm.Md, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +nx: Pr.Next) ->
  {BN.snx(Norm.out(OSt(o, m, src, pd, eof, back, fa, wp, asked, fneed), nx)) == nx : Pr.Next}:
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
    {BN.snx(Norm.out.left(o, m, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx)) == nx : Pr.Next}
  ok_nx(Norm.md.take(m, DO.lsum(src)), o, src, pd, eof, back, fa, wp, asked, fneed, nx)

# take keeps the mode (what fast_left reads of it).
def fl_mbk(q: (D.Bytes & List<&2, B.Note>) & NR.Run, +f: Bool) -> {BN.fast_left(tmd(Norm.md.take.k(q)), f) == Bool.not(f) : Bool}:
  match q:
    case (on, run):
      {==}

def fl_msc(c: Norm.Cut2, s: R.RunSt, ns: List<&2, B.Note>, code: Maybe<&2, Nat>, +f: Bool) -> {BN.fast_left(tmd(Norm.ms.take.c(c, s, ns, code)), f) == False{} : Bool}:
  match c:
    case Norm.Cut2{now, later}:
      {==}

def fl_msk(+t: String, s: R.RunSt, code: Maybe<&2, Nat>, +f: Bool) -> {BN.fast_left(tmd(Norm.ms.take.k(t, s, code)), f) == False{} : Bool}:
  match s:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      fl_msc(Norm.take_w(t, 1073741824), R.RunSt{n, i, h, c, e, l, b, k, o, Nil{}, x}, ns, code, f)

def fl_take(m: Norm.Md, +n: U32, +f: Bool) -> {BN.fast_left(tmd(Norm.md.take(m, n)), f) == BN.fast_left(m, f) : Bool}:
  match m:
    case Norm.MB{run}:
      fl_mbk(NR.take(run, n), f)
    case Norm.MS{s, qs, ql, code}:
      fl_msk(Norm.cat(List.reverse(&2, String, qs)), s, code, f)

# WA and bi of a state, without its run: WA reads only whether the fast path
# may still ask (fl).
def WA0(+fa: List<&2, B.Contig>, +fl: Bool, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +cs: List<&2, String>) -> Nat:
  BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), asked, BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs))

# out keeps WA.
def o_was(+md: S.MdP, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +nx: Pr.Next, +cs: List<&2, String>) ->
  {BN.WAS(fa, BN.sst(Norm.out(OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed), nx)), cs) == WA0(fa, BN.fast_left(S.mkMd(md), fneed), src, pd, eof, back, wp, asked, cs) : Nat}:
  %Equal.sym(Norm.St, BN.sst(Norm.out(OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed), nx)), OSt(o, tmd(Norm.md.take(S.mkMd(md), DO.lsum(src))), src, pd, eof, back, fa, wp, asked, fneed), o_st(S.mkMd(md), o, src, pd, eof, back, fa, wp, asked, fneed, nx)) :
    {BN.WAS(fa, _, cs) == WA0(fa, BN.fast_left(S.mkMd(md), fneed), src, pd, eof, back, wp, asked, cs) : Nat}
  %Equal.sym(Bool, BN.fast_left(tmd(Norm.md.take(S.mkMd(md), DO.lsum(src))), fneed), BN.fast_left(S.mkMd(md), fneed), fl_take(S.mkMd(md), DO.lsum(src), fneed)) :
    {WA0(fa, _, src, pd, eof, back, wp, asked, cs) == WA0(fa, BN.fast_left(S.mkMd(md), fneed), src, pd, eof, back, wp, asked, cs) : Nat}
  {==}

def o_bi(+md: S.MdP, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +nx: Pr.Next, +cs: List<&2, String>) ->
  {BN.biS(BN.sst(Norm.out(OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed), nx)), cs) == BN.biS(OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed), cs) : Bool}:
  %Equal.sym(Norm.St, BN.sst(Norm.out(OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed), nx)), OSt(o, tmd(Norm.md.take(S.mkMd(md), DO.lsum(src))), src, pd, eof, back, fa, wp, asked, fneed), o_st(S.mkMd(md), o, src, pd, eof, back, fa, wp, asked, fneed, nx)) :
    {BN.biS(_, cs) == BN.biS(OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed), cs) : Bool}
  {==}

# R3.
def out_was(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +nx: Pr.Next) ->
  {BN.WAS(fa, BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs) == BN.WAS(fa, S.mkSt(fa, p), cs) : Nat}:
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      o_was(md, o, src, pd, eof, back, fa, wp, asked, fneed, nx, cs)

def out_bi(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +nx: Pr.Next) ->
  {BN.biS(BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs) == BN.biS(S.mkSt(fa, p), cs) : Bool}:
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      o_bi(md, o, src, pd, eof, back, fa, wp, asked, fneed, nx, cs)

def out_snx(+fa: List<&2, B.Contig>, +p: S.StP, +nx: Pr.Next) -> {BN.snx(Norm.out(S.mkSt(fa, p), nx)) == nx : Pr.Next}:
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      o_nx(S.mkMd(md), o, src, pd, eof, back, fa, wp, asked, fneed, nx)

# ---------------------------------------------------------------------------
# The end of the run (R4)
# ---------------------------------------------------------------------------

# bi of a state, without its run (bi does not read it).
def BIo(+src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +cs: List<&2, String>) -> Bool:
  BN.bi.ls(back, PC.mkWin(fa, wp), asked, BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs))

def OL(+O: String, +t: String) -> {Nat.is_le(String.length(O), String.length(String.append(O, t))) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(String.length(O), z) == True{} : Bool}, Nat.add(String.length(O), String.length(t)), String.length(String.append(O, t)),
    Equal.sym(Nat, String.length(String.append(O, t)), Nat.add(String.length(O), String.length(t)), G.slen_app(O, t)), N.le_add_r(String.length(O), String.length(t)))

# HO never grows.
def hoa(+T: R.Report, +O: String, +t: String) -> {Nat.is_le(BN.HO(T, String.append(O, t)), BN.HO(T, O)) == True{} : Bool}:
  HO.ho_anti(String.length(R.Report.out(T)), String.length(O), String.length(String.append(O, t)), 256n, {==}, OL(O, t))

# Finish: no reads, WA as it was.
def fin_ar(+T: R.Report, +O: String, +t: String, +W0: Nat, +r: Nat, +w: Nat, +er: {0n == r : Nat}, +ew: {W0 == w : Nat}) ->
  {Nat.is_le(Nat.add(BN.HO(T, String.append(O, t)), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool}:
  +H2 = BN.HO(T, String.append(O, t))
  +h1 = N.le_add_mono_r(W0, H2, BN.HO(T, O), hoa(T, O, t))
  AB.subst(Nat, z => {Nat.is_le(Nat.add(H2, Nat.add(z, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool}, 0n, r, er,
    AB.subst(Nat, z => {Nat.is_le(Nat.add(H2, Nat.add(0n, z)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool}, W0, w, ew, h1))

# A hand-out of at least 256 bytes and Ask{[]}: one step, paid by HO.
def ask_ar(+T: R.Report, +O: String, +t: String, +W0: Nat, +r: Nat, +w: Nat,
  +hl: {Nat.is_le(256n, String.length(t)) == True{} : Bool},
  +hp: {Nat.is_le(String.length(String.append(O, t)), String.length(R.Report.out(T))) == True{} : Bool},
  +er: {1n == r : Nat}, +ew: {W0 == w : Nat}) ->
  {Nat.is_le(Nat.add(BN.HO(T, String.append(O, t)), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool}:
  +X = String.length(R.Report.out(T))
  +el = G.slen_app(O, t)
  +hp2 = AB.subst(Nat, z => {Nat.is_le(z, X) == True{} : Bool}, String.length(String.append(O, t)), Nat.add(String.length(O), String.length(t)), el, hp)
  +hd = HO.ho_drop(X, String.length(O), String.length(t), 256n, {==}, hl, hp2)
  +hd2 = AB.subst(Nat, z => {Nat.is_le(1n+Nat.div(Nat.sub(X, z), 256n), BN.HO(T, O)) == True{} : Bool}, Nat.add(String.length(O), String.length(t)), String.length(String.append(O, t)),
    Equal.sym(Nat, String.length(String.append(O, t)), Nat.add(String.length(O), String.length(t)), el), hd)
  +H2 = BN.HO(T, String.append(O, t))
  +h3 = N.le_add_mono_r(W0, 1n+H2, BN.HO(T, O), hd2)
  +h4 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(BN.HO(T, O), W0)) == True{} : Bool}, 1n+Nat.add(H2, W0), Nat.add(H2, 1n+W0), Equal.sym(Nat, Nat.add(H2, 1n+W0), 1n+Nat.add(H2, W0), N.add_succ(H2, W0)), h3)
  AB.subst(Nat, z => {Nat.is_le(Nat.add(H2, Nat.add(z, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool}, 1n, r, er,
    AB.subst(Nat, z => {Nat.is_le(Nat.add(H2, Nat.add(1n, z)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool}, W0, w, ew, h4))

# take_w(s, w) of a text longer than w hands out w characters, so at least
# m <= w of them; 256 for the String mode's 2^30.
def tw_eq.go(+s: String, +z: Bool, +w: U32, +hz: {U32.is_zero(w) == z : Bool}, +hf: {Norm.len_le.go(s, z, w) == False{} : Bool}) ->
  {String.length(Norm.Cut2.now(Norm.take_w.go(s, z, w))) == U32.to_nat(w) : Nat}:
  match s z:
    case SNil{} _:
      Empty.absurd({String.length(Norm.Cut2.now(Norm.take_w.go(SNil{}, z, w))) == U32.to_nat(w) : Nat}, N.true_ne_false(hf))
    case SCon{+ch, +t} True{}:
      Equal.sym(Nat, U32.to_nat(w), 0n, LIT.w_zero(w, hz))
    case SCon{+ch, +t} False{}:
      +kk = Norm.take_w.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32))
      +x = U32.to_nat(w)
      +ih = tw_eq.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32), {==}, hf)
      +e2 = Equal.trans(Nat, String.length(Norm.Cut2.now(kk)), U32.to_nat((w - 1 : U32)), Nat.sub(x, 1n), ih, LIT.w_dec(w, hz))
      %Equal.sym(Norm.Cut2, Norm.take_w.cons(ch, kk), Norm.Cut2{SCon{ch, Norm.Cut2.now(kk)}, Norm.Cut2.later(kk)}, LIT.tw_cons(ch, kk)) :
        {String.length(Norm.Cut2.now(_)) == U32.to_nat(w) : Nat}
      Equal.trans(Nat, 1n+String.length(Norm.Cut2.now(kk)), Nat.add(1n, Nat.sub(x, 1n)), x,
        Equal.cong(Nat, Nat, y => 1n+y, String.length(Norm.Cut2.now(kk)), Nat.sub(x, 1n), e2), N.le_sub_add(1n, x, LIT.w_le1(w, hz)))

def lo_g(+s: String, +w: U32, +m: U32, +hm: {U32.is_le(m, w) == True{} : Bool}, +hf: {Norm.len_le(s, w) == False{} : Bool}) ->
  {Nat.is_le(U32.to_nat(m), String.length(Norm.Cut2.now(Norm.take_w(s, w)))) == True{} : Bool}:
  +ee = tw_eq.go(s, U32.is_zero(w), w, {==}, hf)
  +h1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(m), U32.to_nat(w)), U32.is_le(m, w), True{}, Equal.sym(Bool, U32.is_le(m, w), Nat.is_le(U32.to_nat(m), U32.to_nat(w)), U.is_le_to_nat(m, w)), hm)
  AB.subst(Nat, y => {Nat.is_le(U32.to_nat(m), y) == True{} : Bool}, U32.to_nat(w), String.length(Norm.Cut2.now(Norm.take_w(s, w))),
    Equal.sym(Nat, String.length(Norm.Cut2.now(Norm.take_w(s, w))), U32.to_nat(w), ee), h1)

def le_c256(+y: Nat, +h: {Nat.is_le(U32.to_nat(256), y) == True{} : Bool}) -> {Nat.is_le(256n, y) == True{} : Bool}:
  h

def lo(+s: String, +hz: {Norm.len_le(s, 1073741824) == False{} : Bool}) ->
  {Nat.is_le(256n, String.length(Norm.Cut2.now(Norm.take_w(s, 1073741824)))) == True{} : Bool}:
  le_c256(String.length(Norm.Cut2.now(Norm.take_w(s, 1073741824))), lo_g(s, 1073741824, 256, {==}, hz))

# The left part of a byte string is bytes.
def bytes_l(+a: String, +b: String, +h: {E.is_bytes(String.append(a, b)) == True{} : Bool}) -> {E.is_bytes(a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+ch, +t}:
      +h1 = PB.and_true_l(U32.is_lt(Char.to_u32(ch), 256), E.is_bytes(String.append(t, b)), h)
      +h2 = PB.and_true_r(U32.is_lt(Char.to_u32(ch), 256), E.is_bytes(String.append(t, b)), h)
      LM.and_mk(U32.is_lt(Char.to_u32(ch), 256), E.is_bytes(t), h1, bytes_l(t, b, h2))

def mget(m: Maybe<&2, String>) -> String:
  match m:
    case Some{+v}:
      v
    case None{}:
      ""

# The byte mode's Finish.
def bud_mbk(q: (D.Bytes & List<&2, B.Note>) & NR.Run, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +code: Nat, +T: R.Report, +cs: List<&2, String>, +O: String, +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, Bool.not(fneed), src, pd, eof, back, wp, asked, cs), Norm.out.k(Norm.md.take.k(q), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Finish{code})):
  match q:
    case ((bb, nn), run):
      (hbi, +t => ht => hp => +r => er => +w => ew => fin_ar(T, O, t, WA0(fa, Bool.not(fneed), src, pd, eof, back, wp, asked, cs), r, w, er, ew))

def fb_mb(p0: NR.Run & Nat, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +T: R.Report, +cs: List<&2, String>, +O: String, +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, Bool.not(fneed), src, pd, eof, back, wp, asked, cs), Norm.fin.mb(o, p0, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match p0:
    case (run, +code):
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
        BD.BudS(fa, T, cs, O, WA0(fa, Bool.not(fneed), src, pd, eof, back, wp, asked, cs), Norm.out.left(o, Norm.MB{run}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Finish{code}))
      bud_mbk(NR.take(run, DO.lsum(src)), o, src, pd, eof, back, fa, wp, asked, fneed, code, T, cs, O, hbi)

# The String mode's Finish (the queue fits one hand-out).
def bud_msf(+cc: Norm.Cut2, +rs: R.RunSt, +ns: List<&2, B.Note>, +cd: Maybe<&2, Nat>, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +code: Nat, +T: R.Report, +cs: List<&2, String>, +O: String, +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.out.k(Norm.ms.take.c(cc, rs, ns, cd), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Finish{code})):
  match cc:
    case Norm.Cut2{+now, +later}:
      (hbi, +t => ht => hp => +r => er => +w => ew => fin_ar(T, O, t, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), r, w, er, ew))

# The String mode's hand-out of 2^30 bytes, then Ask{[]}.
def bud_ask.k(+o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o2: String, +ns: List<&2, B.Note>, +x: Bool, +Q: List<&2, String>, +cd: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +T: R.Report, +cs: List<&2, String>, +O: String, +now: String, +later: String,
  os: &ol: U32 -> &ot: AT.Tree<U32> -> &d: Nat -> ({NR.of_str(now) == C.BT(ol, ot) : D.Bytes}
    & ({D.ok(C.BT(ol, ot), d) == True{} : Bool} & {NR.chars(D.view(C.BT(ol, ot))) == now : String})),
  +hl: {Nat.is_le(256n, String.length(now)) == True{} : Bool},
  +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.out.k(Norm.ms.take.c(Norm.Cut2{now, later}, R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, ns, Some{cd}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Ask{Nil{}})):
  (+ol, os1) = os
  (+ot, os2) = os1
  (+d, os3) = os2
  (+e1, os4) = os3
  (+eok, ech) = os4
  +eout = Equal.trans(Maybe<&2, String>, E.out(NR.of_str(now)), E.out(C.BT(ol, ot)), Some{now},
    Equal.cong(D.Bytes, Maybe<&2, String>, z => E.out(z), NR.of_str(now), C.BT(ol, ot), e1),
    Equal.trans(Maybe<&2, String>, E.out(C.BT(ol, ot)), Some{E.chars(D.view(C.BT(ol, ot)))}, Some{now},
      ENC.out_ok(ol, ot, d, eok, C.ok_d(ol, ot, d, eok)),
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(ol, ot))), now,
        Equal.trans(String, E.chars(D.view(C.BT(ol, ot))), NR.chars(D.view(C.BT(ol, ot))), now, DO.chars_nr(D.view(C.BT(ol, ot))), ech))))
  (hbi, +t => ht => hp => +r => er => +w => ew =>
    +es = Equal.trans(Maybe<&2, String>, Some{t}, E.out(NR.of_str(now)), Some{now}, Equal.sym(Maybe<&2, String>, E.out(NR.of_str(now)), Some{t}, ht), eout)
    +et = Equal.cong(Maybe<&2, String>, String, z => mget(z), Some{t}, Some{now}, es)
    +hlt = AB.subst(String, y => {Nat.is_le(256n, String.length(y)) == True{} : Bool}, now, t, Equal.sym(String, t, now, et), hl)
    ask_ar(T, O, t, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), r, w, hlt, hp, er, ew))

def bud_ask(+o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o2: String, +ns: List<&2, B.Note>, +x: Bool, +Q: List<&2, String>, +ql2: Nat, +cd: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +T: R.Report, +cs: List<&2, String>, +O: String,
  +hz: {Norm.len_le(Norm.cat(List.reverse(&2, String, Q)), 1073741824) == False{} : Bool},
  +hq: {E.is_bytes(Norm.cat(List.reverse(&2, String, Q))) == True{} : Bool},
  +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.out(OSt(o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, Q, ql2, Some{cd}}, src, pd, eof, back, fa, wp, asked, fneed), Pr.Ask{Nil{}})):
  +eapp = LIT.tw_app.go(Norm.cat(List.reverse(&2, String, Q)), U32.is_zero(1073741824), 1073741824)
  +hnl = LIT.tw_len.go(Norm.cat(List.reverse(&2, String, Q)), U32.is_zero(1073741824), 1073741824, {==})
  +hbn = bytes_l(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), AB.subst(String, y => {E.is_bytes(y) == True{} : Bool}, Norm.cat(List.reverse(&2, String, Q)), String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824))), Equal.sym(String, String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824))), Norm.cat(List.reverse(&2, String, Q)), eapp), hq))
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
    BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.out.left(o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, Q, ql2, Some{cd}}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Ask{Nil{}}))
  %Equal.sym(Norm.Cut2, Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824), Norm.Cut2{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824))}, DO.cut_eta(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824))) :
    BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.out.k(Norm.ms.take.c(_, R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, ns, Some{cd}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Ask{Nil{}}))
  bud_ask.k(o, n, i, h, c, e, l, b, k, o2, ns, x, Q, cd, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), PR.of_str(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824)), hbn, hnl), lo(Norm.cat(List.reverse(&2, String, Q)), hz), hbi)

# fin.ms.go: Finish when the queue fits a hand-out, else a hand-out and Ask{[]}.
def fms(+z: Bool, +o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o2: String, +ns: List<&2, B.Note>, +x: Bool, +Q: List<&2, String>, +ql2: Nat, +cd: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +T: R.Report, +cs: List<&2, String>, +O: String,
  +hz: {Norm.len_le(Norm.cat(List.reverse(&2, String, Q)), 1073741824) == z : Bool},
  +hq: {E.is_bytes(Norm.cat(List.reverse(&2, String, Q))) == True{} : Bool},
  +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.fin.ms.go(z, o, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, Q, ql2, cd, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match z:
    case True{}:
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
        BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.out.left(o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, Q, ql2, Some{cd}}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, Pr.Finish{cd}))
      bud_msf(Norm.take_w(Norm.cat(List.reverse(&2, String, Q)), 1073741824), R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, ns, Some{cd}, o, src, pd, eof, back, fa, wp, asked, fneed, cd, T, cs, O, hbi)
    case False{}:
      bud_ask(o, n, i, h, c, e, l, b, k, o2, ns, x, Q, ql2, cd, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, hz, hq, hbi)

def fb_some(+s: R.RunSt, +Q: List<&2, String>, +ql2: Nat, +cd: Nat, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +T: R.Report, +cs: List<&2, String>, +O: String,
  +hq: {E.is_bytes(Norm.cat(List.reverse(&2, String, Q))) == True{} : Bool},
  +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.fin.ms.go(Norm.len_le(Norm.cat(List.reverse(&2, String, Q)), 1073741824), o, s, Q, ql2, cd, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}:
      fms(Norm.len_le(Norm.cat(List.reverse(&2, String, Q)), 1073741824), o, n, i, h, c, e, l, b, k, o2, ns, x, Q, ql2, cd, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, {==}, hq, hbi)

def fb_none(+rep: R.Report, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +T: R.Report, +cs: List<&2, String>, +O: String,
  +hbr: {E.is_bytes(R.Report.out(rep)) == True{} : Bool},
  +hq: {E.is_bytes(Norm.cat(List.reverse(&2, String, qs))) == True{} : Bool},
  +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, WA0(fa, False{}, src, pd, eof, back, wp, asked, cs), Norm.fin.ms(rep, o, s, qs, ql, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match rep s:
    case R.Report{+out, +nr, +code} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns0, +x}:
      +hq2 = AB.subst(String, y => {E.is_bytes(y) == True{} : Bool}, String.append(Norm.cat(List.reverse(&2, String, qs)), out), Norm.cat(List.reverse(&2, String, out <> qs)),
        Equal.sym(String, Norm.cat(List.reverse(&2, String, out <> qs)), String.append(Norm.cat(List.reverse(&2, String, qs)), out), DF.cat_rev_cons(out, qs)),
        DF.bytes_app(Norm.cat(List.reverse(&2, String, qs)), out, hq, hbr))
      fms(Norm.len_le(Norm.cat(List.reverse(&2, String, out <> qs)), 1073741824), o, n, i, h, c, e, l, b, k, "", nr, x, out <> qs, Nat.add(ql, String.length(out)), code, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, {==}, hq2, hbi)

def fb_md(+md: S.MdP, +o: B.Opts, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +T: R.Report, +cs: List<&2, String>, +O: String,
  +hmd: {S.md_ok(md) == True{} : Bool},
  +hbi: {BIo(src, pd, eof, back, fa, wp, asked, fneed, cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, BN.WAS(fa, OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed), cs), Norm.finish(OSt(o, S.mkMd(md), src, pd, eof, back, fa, wp, asked, fneed))):
  match md:
    case S.MBP{+rp}:
      fb_mb(NR.finish(P.mkRun(rp), R.Opts.w(o)), o, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, hbi)
    case S.MSP{+s, +qs, +ql, None{}}:
      +CQ = Norm.cat(List.reverse(&2, String, qs))
      +hq = DO.z6_2(Nat.is_eq(ql, String.length(CQ)), E.is_bytes(CQ), P.st_bytes(s), String.is_empty(P.RunSt.out(s)), Bool.or(R.RunSt.inbody(s), String.is_empty(CQ)), Bool.or(R.RunSt.inbody(s), List.is_empty(&2, B.Note, P.RunSt.notes(s))), hmd)
      +hsb = DO.z6_3(Nat.is_eq(ql, String.length(CQ)), E.is_bytes(CQ), P.st_bytes(s), String.is_empty(P.RunSt.out(s)), Bool.or(R.RunSt.inbody(s), String.is_empty(CQ)), Bool.or(R.RunSt.inbody(s), List.is_empty(&2, B.Note, P.RunSt.notes(s))), hmd)
      fb_none(R.finish(s), s, qs, ql, o, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, DF.fin_out_bytes(s, hsb), hq, hbi)
    case S.MSP{+s, +qs, +ql, Some{+cd}}:
      +CQ = Norm.cat(List.reverse(&2, String, qs))
      +hq = DO.z6_2(Nat.is_eq(ql, String.length(CQ)), E.is_bytes(CQ), P.st_bytes(s), String.is_empty(P.RunSt.out(s)), Bool.or(R.RunSt.inbody(s), String.is_empty(CQ)), Bool.or(R.RunSt.inbody(s), List.is_empty(&2, B.Note, P.RunSt.notes(s))), hmd)
      fb_some(s, qs, ql, cd, o, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, hq, hbi)

# R4.
def fin_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP,
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.BudS(fa, T, cs, O, BN.WAS(fa, S.mkSt(fa, p), cs), Norm.finish(S.mkSt(fa, p))):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      fb_md(md, o, src, pd, eof, back, fa, wp, asked, fneed, T, cs, O, DO.wf_md(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}, hw), hbi)
