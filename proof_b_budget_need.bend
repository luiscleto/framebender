import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import lawful-bytes@0.1.0.0/defs.bend as D

# The budget's potential (notes/bytes_proofs_budget.md, "The potential, as
# defined"). The API (proof_b_budget_api.bend) defines need and bi as these.
#
#   need = |cs| + [not eof] + 2       pieces, the end of the file, Finish and
#                                     the driver's last step
#        + HO(T, O)                   yields and hand-outs still to come: each
#                                     writes at least 256 bytes (2^30, in fact)
#        + RD(nx)                     a pending Ask{rs}: its step and |rs| reads
#        + WA(fa, p, cs)              the Wants of the lines still to come
#
# WA gives each line that can Want (one not malformed) the allowance
#   LA = 2 RW + 2 ZW,  RW = 1 + max(1, |REF|),  ZW = 2 + FM(fa)
# for at most two Req.of windows (the fast path's, once fneed is set; the
# slow path's first try, once H1 holds; at most max(1, |REF|) reads each)
# and at most two zero windows (the slow path's
# miss once back >= 1, and vd.x's once tries run out; at most
# max(1, POS + |REF|) <= 1 + FM reads each, REF fitting its contig). The
# line being handled (the first line of the text still to come) has only
# what its state has not used: RW while the fast path may ask (byte mode,
# fneed False), RW while its Req.of window is neither held nor asked, ZW
# while back = 0, ZW while back < POS.

# The longest contig.
def FM(fa: List<&2, B.Contig>) -> Nat:
  match fa:
    case Nil{}:
      0n
    case Con{B.Contig{nm, +r}, t}:
      Nat.max(String.length(r), FM(t))

def max1(+x: Nat) -> Nat:
  Nat.max(1n, x)

# A line's fields as the machine keeps them (J.pfs), and what its Wants use.
def lfs(+l: B.Line) -> List<&2, String>:
  J.pfs(B.Line.body(l))

# The line can Want: it is not malformed.
def lgate(+l: B.Line) -> Bool:
  Bool.not(B.Rec.malformed(lfs(l)))

def lchrom(+l: B.Line) -> String:
  B.Rec.field(lfs(l), 0n)

def lpos(+l: B.Line) -> Nat:
  B.Rec.pos(lfs(l))

def lref(+l: B.Line) -> Nat:
  String.length(B.Rec.field(lfs(l), 3n))

# The slow path's first window: POS - 1 up to the end of REF.
def lp1(+l: B.Line) -> Nat:
  Nat.sub(lpos(l), 1n)

def lend(+l: B.Line) -> Nat:
  Nat.add(lp1(l), lref(l))

def RW(+l: B.Line) -> Nat:
  1n+max1(lref(l))

def ZW(+fa: List<&2, B.Contig>) -> Nat:
  2n+FM(fa)

def pick(b: Bool, +n: Nat) -> Nat:
  Bool.pick(Nat, b, n, 0n)

# A line's whole allowance.
def LA(+fa: List<&2, B.Contig>, +l: B.Line) -> Nat:
  pick(lgate(l), Nat.add(Nat.add(RW(l), RW(l)), Nat.add(ZW(fa), ZW(fa))))

def LAs(+fa: List<&2, B.Contig>, ls: List<&2, B.Line>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(LA(fa, l), LAs(fa, t))

# ---------------------------------------------------------------------------
# On the machine state (so every picture of a state has the same need)
# ---------------------------------------------------------------------------

# The text a state's sources hold (P.srcstext on mkSrcs), and its line end
# (P.pdtext on mkPd).
def srcT(src: List<&1, Norm.Src>) -> String:
  match src:
    case Nil{}:
      ""
    case Con{Norm.SB{b, +at}, t}:
      String.append(NR.chars(List.drop(&2, U32, D.view(b), U32.to_nat(at))), srcT(t))
    case Con{Norm.SL{+p}, t}:
      String.append(p ++ "\n", srcT(t))
    case Con{Norm.SP{b, +at}, t}:
      srcT(t)
    case Con{Norm.SR{l}, t}:
      srcT(t)


def pdT(pd: Norm.Pd) -> String:
  match pd:
    case Norm.PB{b}:
      NR.chars(D.view(b))
    case Norm.PS{+s}:
      s

# serve's test: the window holds the read c, a .. b.
def holdsW(w: Norm.Win, +c: String, +a: Nat, +b: Nat) -> Bool:
  match w:
    case Norm.WNone{}:
      False{}
    case Norm.WUnk{+c0}:
      String.eq(c0, c)
    case Norm.WKnown{+c0, cb, +a0, +b0, +clen, off, raw, offu, rlen, clenu}:
      String.eq(c0, c) && Nat.is_le(a0, a) && Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen))
    case Norm.WStr{+c0, +a0, +b0, +clen, off, raw}:
      String.eq(c0, c) && Nat.is_le(a0, a) && Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen))

# A pending Ask's window (contig, first start, last end) covers c, a .. b.
def coversA(m: Maybe<&2, List<&2, Pr.Req>>, +c: String, +a: Nat, +b: Nat) -> Bool:
  match m:
    case Some{Pr.Req{+c0, +a0, +b0} <> t}:
      String.eq(c0, c) && Nat.is_le(a0, a) && Nat.is_le(b, Norm.last_b(t, b0))
    case _:
      False{}

# The read is held: by the pending Ask's window while one is pending (set_win
# replaces the window by it), else by the window.
def heldA(w: Norm.Win, m: Maybe<&2, List<&2, Pr.Req>>, +c: String, +a: Nat, +b: Nat) -> Bool:
  match m:
    case Some{+rs}:
      coversA(Some{rs}, c, a, b)
    case None{}:
      holdsW(w, c, a, b)

# The fast path may still ask: byte mode and fneed not set.
def fast_left(md: Norm.Md, +fneed: Bool) -> Bool:
  match md:
    case Norm.MB{run}:
      Bool.not(fneed)
    case Norm.MS{s, qs, ql, code}:
      False{}

# What the line being handled has left.
def rem(+fa: List<&2, B.Contig>, +fl: Bool, +back: Nat, w: Norm.Win, m: Maybe<&2, List<&2, Pr.Req>>, +l: B.Line) -> Nat:
  pick(lgate(l), Nat.add(Nat.add(pick(fl, RW(l)), pick(Bool.not(heldA(w, m, lchrom(l), lp1(l), lend(l))), RW(l))),
    Nat.add(pick(Nat.is_eq(back, 0n), ZW(fa)), pick(Nat.is_lt(back, lpos(l)), ZW(fa)))))

def WA.ls(+fa: List<&2, B.Contig>, +fl: Bool, +back: Nat, w: Norm.Win, m: Maybe<&2, List<&2, Pr.Req>>, ls: List<&2, B.Line>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case +l <> t:
      Nat.add(rem(fa, fl, back, w, m, l), LAs(fa, t))

# The lines still to come: the sources', the line end's, then (before the
# end of the file) the pieces not given yet (S.intext on mkSt).
def lines(src: List<&1, Norm.Src>, pend: Norm.Pd, +eof: Bool, +cs: List<&2, String>) -> List<&2, B.Line>:
  B.Text.lines(String.append(srcT(src), String.append(pdT(pend), S.concat_if(eof, cs))))

# Hand-outs and yields still to come.
def HO(+T: R.Report, +O: String) -> Nat:
  Nat.div(Nat.sub(String.length(R.Report.out(T)), String.length(O)), 256n)

# A pending Ask: its step and its reads.
def RD(nx: Pr.Next) -> Nat:
  match nx:
    case Pr.Ask{+rs}:
      1n+List.length(&2, Pr.Req, rs)
    case _:
      0n

# Every line still to come, in the order the machine handles them: the
# records of a split line in front (-m: SP, a buffer of whole records; SR,
# one record), then the input's own lines (lines).
def ALL(src: List<&1, Norm.Src>, pend: Norm.Pd, +eof: Bool, +cs: List<&2, String>) -> List<&2, B.Line>:
  match src:
    case Nil{}:
      lines(Nil{}, pend, eof, cs)
    case Con{Norm.SB{b, +at}, t}:
      lines(Con{Norm.SB{b, at}, t}, pend, eof, cs)
    case Con{Norm.SL{+p}, t}:
      lines(Con{Norm.SL{p}, t}, pend, eof, cs)
    case Con{Norm.SP{b, +at}, t}:
      List.append(&2, B.Line, B.Text.lines(NR.chars(List.drop(&2, U32, D.view(b), U32.to_nat(at)))), ALL(t, pend, eof, cs))
    case Con{Norm.SR{+l}, t}:
      l <> ALL(t, pend, eof, cs)

# The number of ALTs of a line (LAWS.bend's n_alts of its body).
def nalts(+l: B.Line) -> Nat:
  List.length(&2, String, B.Rec.alts(B.Rec.fields(B.Line.body(l))))

# The line may be split by -m (Rec.parts' test: -m, not malformed, two or
# more ALTs).
def cand(+o: B.Opts, +l: B.Line) -> Bool:
  R.Opts.split(o) && Bool.not(B.Rec.malformed(B.Rec.fields(B.Line.body(l)))) && Nat.is_le(2n, nalts(l))

# A line that may be split holds one more allowance per ALT, for its records
# (decisions 31 and 34: 1 + k allowances per candidate line).
def xa(+o: B.Opts, +fa: List<&2, B.Contig>, +l: B.Line) -> Nat:
  pick(cand(o, l), Nat.mul(nalts(l), LA(fa, l)))

def XA(+o: B.Opts, +fa: List<&2, B.Contig>, ls: List<&2, B.Line>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case +l <> t:
      Nat.add(xa(o, fa, l), XA(o, fa, t))

# WA and XA of the lines still to come.
def WAX(+fa: List<&2, B.Contig>, +o: B.Opts, +fl: Bool, +back: Nat, w: Norm.Win, m: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>) -> Nat:
  Nat.add(WA.ls(fa, fl, back, w, m, ls), XA(o, fa, ls))

def WAS(+fa: List<&2, B.Contig>, st: Norm.St, +cs: List<&2, String>) -> Nat:
  match st:
    case Norm.St{+o, md, src, pend, +eof, +back, win, asked, +fneed, +dfs}:
      WAX(fa, o, fast_left(md, fneed), back, win, asked, ALL(src, pend, eof, cs))

def needS(+fa: List<&2, B.Contig>, +T: R.Report, st: Norm.St, +cs: List<&2, String>, +eof: Bool, +nx: Pr.Next, +O: String) -> Nat:
  Nat.add(Nat.add(List.length(&2, String, cs), pick(Bool.not(eof), 1n)),
    Nat.add(2n, Nat.add(HO(T, O), Nat.add(RD(nx), WAS(fa, st, cs)))))

# The invariant: once back has grown (a zero window was asked for the line
# being handled), that window is held or asked, and REF fits its contig (the
# window's clen).
def zfit(w: Norm.Win, +c: String, +e: Nat) -> Bool:
  match w:
    case Norm.WKnown{+c0, cb, a0, b0, +clen, off, raw, offu, rlen, clenu}:
      String.eq(c0, c) && Nat.is_le(e, clen)
    case Norm.WStr{+c0, a0, b0, +clen, off, raw}:
      String.eq(c0, c) && Nat.is_le(e, clen)
    case _:
      False{}

def zheld(w: Norm.Win, +c: String, +e: Nat) -> Bool:
  match w:
    case Norm.WKnown{+c0, cb, +a0, +b0, +clen, off, raw, offu, rlen, clenu}:
      String.eq(c0, c) && Nat.is_le(a0, 0n) && Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen)) && Nat.is_le(e, clen)
    case Norm.WStr{+c0, +a0, +b0, +clen, off, raw}:
      String.eq(c0, c) && Nat.is_le(a0, 0n) && Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen)) && Nat.is_le(e, clen)
    case _:
      False{}

def heldZ(w: Norm.Win, m: Maybe<&2, List<&2, Pr.Req>>, +c: String, +e: Nat) -> Bool:
  match m:
    case Some{+rs}:
      zfit(w, c, e) && coversA(Some{rs}, c, 0n, e)
    case None{}:
      zheld(w, c, e)

def bi.ls(+back: Nat, w: Norm.Win, m: Maybe<&2, List<&2, Pr.Req>>, ls: List<&2, B.Line>) -> Bool:
  match ls:
    case Nil{}:
      Nat.is_eq(back, 0n)
    case +l <> t:
      Nat.is_eq(back, 0n) || heldZ(w, m, lchrom(l), lend(l))

def biS(st: Norm.St, +cs: List<&2, String>) -> Bool:
  match st:
    case Norm.St{o, md, src, pend, +eof, +back, win, asked, fneed, +dfs}:
      bi.ls(back, win, asked, ALL(src, pend, eof, cs))

# The API's need and bi: on the state a picture stands for.
def need(+fa: List<&2, B.Contig>, +T: R.Report, +p: S.StP, +cs: List<&2, String>, +eof: Bool, +nx: Pr.Next, +O: String) -> Nat:
  needS(fa, T, S.mkSt(fa, p), cs, eof, nx, O)

def bi(+fa: List<&2, B.Contig>, +T: R.Report, +p: S.StP, +cs: List<&2, String>, +eof: Bool, +nx: Pr.Next, +O: String) -> Bool:
  biS(S.mkSt(fa, p), cs)

# What a step produces (the API's sst, snx, sns, sout forward to these).
def sst(s: Norm.Step) -> Norm.St:
  match s:
    case Norm.Step{st, b, ns, nx}:
      st

def snx(s: Norm.Step) -> Pr.Next:
  match s:
    case Norm.Step{st, b, ns, nx}:
      nx

def sns(s: Norm.Step) -> List<&2, B.Note>:
  match s:
    case Norm.Step{st, b, ns, nx}:
      ns

def sout(s: Norm.Step) -> Maybe<&2, String>:
  match s:
    case Norm.Step{st, b, ns, nx}:
      E.out(b)
