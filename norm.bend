import Base
import ./types.bend as B
import ./protocol.bend as P
import ./run.bend as R
import ./norm_line.bend as J
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/fast.bend as F

# ---------------------------------------------------------------------------
# The state
# ---------------------------------------------------------------------------

# A buffer whose lines from at on are not handled yet.
type Src is Type:
  Src{b: D.Bytes, at: U32}

# The last reference answer, kept to answer later reads from it.
#   WUnk: contig c is not in the reference.
#   WKnown: the answer to the read of c from a up to b: c's length clen, and
#     its letters from off (as P.Known); cb: c's bytes; offu, rlen, clenu:
#     off, raw's length and clen as U32 (clenu 0 when they do not fit).
type Win is Type:
  WNone{}
  WUnk{c: String}
  WKnown{c: String, cb: D.Bytes, a: Nat, b: Nat, clen: Nat, off: Nat, raw: D.Bytes, offu: U32, rlen: U32, clenu: U32}

# The machine's state: the options; the run (norm_run.bend); the buffers
# whose lines are not handled yet; the end of a line not yet complete
# (pend); whether the file ended; how far back the next reference read for
# the waiting line starts; the last reference answer; the read asked last.
type St is Type:
  St{o: B.Opts, run: NR.Run, src: List<&1, Src>, pend: D.Bytes, eof: Bool, back: Nat, win: Win, asked: Maybe<&2, P.Req>}

# How the program starts: with the state and the paths of the FASTA and VCF
# files, or with a usage error.
type Begin is Type:
  Begin{st: St, ref: String, vcf: String}
  Usage{}

# One step: the new state, the bytes for stdout, messages for stderr, what
# next.
type Step is Type:
  Step{st: St, out: D.Bytes, notes: List<&2, B.Note>, next: P.Next}

# What handling the next line led to.
#   Went: a line was handled (or a piece moved to pend).
#   Want: the line needs a reference read.
#   Idle: no complete line is left.
#   Ended: the run has stopped.
#   Yield: this step wrote 2^30 bytes or more; the step ends (so that an
#     output buffer stays within 2^31 bytes) and the next one goes on.
type Adv is Type:
  Went{st: St}
  Want{st: St, req: P.Req}
  Idle{st: St}
  Ended{st: St}
  Yield{st: St}

# ---------------------------------------------------------------------------
# Reference reads, answered from the last answer when it holds them
# ---------------------------------------------------------------------------

# A read answered from the last answer (Some), or not (None); clen: the
# contig's length (for grow).
type Sv is Type:
  Sv{win: Win, ans: Maybe<&1, P.Ans>, clen: Nat}

# What the last answer says of a record (CHROM s .. e0-1, REF rl bytes from
# rs, POS pos): Hit: its REF is the reference's (either case), within the
# contig; Need: it is not this contig's, or does not hold REF; Miss: the
# contig is not in the reference, or REF runs past its end, or differs.
type Wr is Data:
  WHit{}
  WNeed{}
  WMiss{}

type Wo is Type:
  Wo{w: Win, b: D.Bytes, r: Wr}

# Reading the reference for a record judged on its text: a window back
# letters before its POS up to the end of its REF, grown until J.fast can
# tell.
#   SAgain: try again with back; SDone: J.fast's verdict; SMiss: the last
#   answer does not hold the window, req asks for it.
type Sx is Type:
  SAgain{win: Win, back: Nat}
  SDone{win: Win, f: J.Fast, back: Nat}
  SMiss{win: Win, req: P.Req, back: Nat}

# framebender: the program (code, not spec). MACHINE.bend states what it must
# do; the law reaches the code through Norm.start and Norm.step.
#
# The input arrives as packed buffers (bytes_enc.bend's enc of each piece).
# Lines are read in place. A record in the current CHROM run that passes the
# fast path's tests (norm_fast.bend, and the CHROM and REF tests here) is
# written as it came: its bytes go to the output buffer, nothing is decoded.
# Every other line is decoded (its text, as bytes_enc.bend's text gives it)
# and handled by the String code (norm_line.bend: J.judge_fs, J.fast).
# notes/bytes.md has the design and the refinement argument.

# The result for one body line through a reference answer (norm_line.bend).
def judge_in(a: Maybe<&1, P.Ans>, +body: String) -> Maybe<&2, B.Res>:
  J.judge_in(a, body)

def start.of(m: Maybe<&2, B.Cfg>) -> Begin:
  match m:
    case None{}:
      Usage{}
    case Some{B.Cfg{o, r, v}}:
      Begin{St{o, NR.start(), Nil{}, BY.empty(0n), False{}, 100n, WNone{}, None{}}, r, v}

# The command line after the program's name.
def start(argv: List<&2, String>) -> Begin:
  start.of(B.Args.parse(argv))

# How many letters a reference read asks for past what the line needs, so
# that the next lines are answered from it.
def ahead() -> Nat:
  16777216n

def margin() -> Nat:
  65536n

# ---------------------------------------------------------------------------
# Text
# ---------------------------------------------------------------------------

def chars(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{x, t}:
      SCon{Chr{x}, chars(t)}

def text.k(r: D.Bytes & List<&2, U32>) -> D.Bytes & String:
  (b, xs) = r
  (b, chars(xs))

# Bytes s .. s+n-1 as text (one Char per byte).
def text(b: D.Bytes, +s: U32, +n: U32) -> D.Bytes & String:
  text.k(BY.to_list(b, s, n))

def ends_cr.go(s: String, h: Char) -> Bool:
  match s:
    case SNil{}:
      Char.is_eq(h, '\r')
    case SCon{h2, t}:
      ends_cr.go(t, h2)

# String.ends_with(s, "\r"), without reversing s.
def ends_cr(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      ends_cr.go(t, h)

# B.Text.line, computed with ends_cr.
def line(+p: String) -> B.Line:
  B.Text.line.if(ends_cr(p), p)

def serve.slice(+c: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, +a2: Nat, r: D.Bytes & D.Bytes) -> Sv:
  (s, raw) = r
  Sv{WKnown{c, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, Some{P.Known{clen, a2, s}}, clen}

def serve.known(hit: Bool, w: Win, +a: Nat, +b: Nat) -> Sv:
  match hit w:
    case True{} WKnown{+c, cb, +a0, +b0, +clen, +off, raw, +offu, +rlen, +clenu}:
      +a2 = Nat.min(a, clen)
      +n = Nat.sub(Nat.min(b, clen), a2)
      serve.slice(c, cb, a0, b0, clen, off, offu, rlen, clenu, a2, NR.put_bytes(BY.empty(0n), raw, U32.from_nat(Nat.sub(a2, off)), U32.from_nat(n)))
    case _ w:
      Sv{w, None{}, 0n}

def serve.unk(hit: Bool, +c0: String) -> Sv:
  match hit:
    case True{}:
      Sv{WUnk{c0}, Some{P.Unknown{}}, 0n}
    case False{}:
      Sv{WUnk{c0}, None{}, 0n}

# The truthful answer to the read of contig c from a up to b, if the last
# answer holds it: the same contig, from no later than a, up to no earlier
# than b (both cut at the contig's end, as truth cuts them).
def serve(w: Win, +c: String, +a: Nat, +b: Nat) -> Sv:
  match w:
    case WNone{}:
      Sv{WNone{}, None{}, 0n}
    case WUnk{+c0}:
      serve.unk(String.eq(c0, c), c0)
    case WKnown{+c0, cb, +a0, +b0, +clen, +off, raw, +offu, +rlen, +clenu}:
      serve.known(String.eq(c0, c) && Nat.is_le(a0, a) && Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen)), WKnown{c0, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, a, b)

def u32_if(+n: Nat) -> U32:
  Bool.pick(U32, Nat.is_lt(n, 2147483648n), U32.from_nat(n), 0)

def win_of.k(+c: String, +a: Nat, +b: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32) -> Win:
  (raw, +rl) = r
  +fits = Nat.is_lt(off, 2147483648n) && Nat.is_lt(clen, 2147483648n)
  WKnown{c, NR.of_str(c), a, b, clen, off, raw, U32.from_nat(off), rl, Bool.pick(U32, fits, U32.from_nat(clen), 0)}

# The answer to the read asked last, kept.
def win_of(m: Maybe<&2, P.Req>, ans: Maybe<&1, P.Ans>) -> Win:
  match m ans:
    case Some{P.Req{+c, +a, +b}} Some{P.Known{+clen, +off, raw}}:
      win_of.k(c, a, b, clen, off, BY.len(raw))
    case Some{P.Req{c, a, b}} Some{P.Unknown{}}:
      WUnk{c}
    case _ _:
      WNone{}

# How far back the next window starts: twice as far, or (once the window is
# as long as the contig) back to the contig's first letter.
def grow(+clen: Nat, +back: Nat, +pos: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(clen, back) && Bool.not(Nat.is_eq(clen, 0n)), pos, Nat.add(Nat.mul(back, 2n), 1n))

# ---------------------------------------------------------------------------
# Lines decoded (header lines and the slow path)
# ---------------------------------------------------------------------------

# The line is done: the input moves past it.
def done(+o: B.Opts, run: NR.Run, p: D.Bytes & String, +at: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (b, s) = p
  Went{St{o, run, Src{b, at} <> rest, pend, eof, 100n, win, None{}}}

def done.b(+o: B.Opts, p: NR.Run & D.Bytes, +at: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, b) = p
  Went{St{o, run, Src{b, at} <> rest, pend, eof, 100n, win, None{}}}

def ticked(run: NR.Run) -> NR.Run & Nat:
  NR.Run.n(NR.tick(run))

# The read asked when the last answer does not hold a .. e: from margin()
# letters earlier (records a little out of order, or a window grown back,
# are then answered from it), and ahead() letters on.
#
# A read asks for at most 2^31 letters (E.reqs_ok). A window that needs more
# (a contig of more than 2^31 letters, read back to its start) is not held,
# and the line is asked for again (notes/bytes.md, limits).
def Req.of(+c: String, +a: Nat, +e: Nat) -> P.Req:
  +a2 = Nat.sub(a, margin())
  P.Req{c, a2, Nat.min(Nat.max(e, Nat.add(a, ahead())), Nat.add(a2, 2147483648n))}

def at_of(+n: Nat, +fs: List<&2, String>) -> B.At:
  B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}

def same_done(+o: B.Opts, p: NR.Run & Nat, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, +n) = p
  done.b(o, NR.same_done(run, o, at_of(n, fs), B.Rec.pos(fs), b, s, (lf + 1 - s : U32)), (lf + 1 : U32), rest, pend, eof, win)

def body_done(r: B.Res, +o: B.Opts, p: NR.Run & Nat, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, +n) = p
  done.b(o, NR.body_line(r, run, o, l, at_of(n, fs), B.Rec.pos(fs), b, s, (lf + 1 - s : U32)), (lf + 1 : U32), rest, pend, eof, win)

def slow.f(+back: Nat, +clen: Nat, +pos: Nat, win: Win, f: J.Fast) -> Sx:
  match f:
    case J.Other{None{}}:
      SAgain{win, grow(clen, back, pos)}
    case f:
      SDone{win, f, back}

def slow.sv(+back: Nat, +req: P.Req, +fs: List<&2, String>, +body: String, sv: Sv) -> Sx:
  match sv:
    case Sv{win, None{}, k}:
      SMiss{win, req, back}
    case Sv{win, Some{ans}, +clen}:
      slow.f(back, clen, B.Rec.pos(fs), win, J.fast(Some{ans}, fs, body))

# One try, with the window back letters before POS.
def slow.try(win: Win, +back: Nat, +fs: List<&2, String>, +body: String) -> Sx:
  +p = Nat.sub(B.Rec.pos(fs), 1n)
  +c = B.Rec.field(fs, 0n)
  +a = Nat.sub(p, back)
  +e = Nat.add(p, String.length(B.Rec.field(fs, 3n)))
  slow.sv(back, Req.of(c, a, e), fs, body, serve(win, c, a, e))

def slow.go(fuel: Nat, x: Sx, +fs: List<&2, String>, +body: String) -> Sx:
  match fuel x:
    case 1n+k SAgain{win, +back}:
      slow.go(k, slow.try(win, back, fs, body), fs, body)
    case _ x:
      x

# (Not reached: the window grows to the whole contig, where J.fast tells.)
def slow.whole(+o: B.Opts, run: NR.Run, +fs: List<&2, String>, +s: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, +back: Nat, win: Win) -> Adv:
  +req = {Req.of(B.Rec.field(fs, 0n), 0n, Nat.add(B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)))) : P.Req}
  Want{St{o, run, Src{b, s} <> rest, pend, eof, back, win, Some{req}}, req}

def slow.end(x: Sx, +o: B.Opts, run: NR.Run, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool) -> Adv:
  match x:
    case SDone{win, J.Same{}, back}:
      same_done(o, ticked(run), l, fs, s, lf, b, rest, pend, eof, win)
    case SDone{win, J.Other{Some{r}}, back}:
      body_done(r, o, ticked(run), l, fs, s, lf, b, rest, pend, eof, win)
    case SMiss{win, +req, +back}:
      Want{St{o, run, Src{b, s} <> rest, pend, eof, back, win, Some{req}}, req}
    case SDone{win, J.Other{None{}}, +back}:
      slow.whole(o, run, fs, s, b, rest, pend, eof, back, win)
    case SAgain{win, +back}:
      slow.whole(o, run, fs, s, b, rest, pend, eof, back, win)

def slow.judge(m: Maybe<&2, B.Res>, +back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  match m:
    case Some{r}:
      body_done(r, o, ticked(run), l, fs, s, lf, b, rest, pend, eof, win)
    case None{}:
      slow.end(slow.go(64n, SAgain{win, back}, fs, B.Line.body(l)), o, run, l, fs, s, lf, b, rest, pend, eof)

# A body line the fast path did not take: judged on its text.
def slow(+back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  +fs = J.pfs(B.Line.body(l))
  slow.judge(J.judge_fs(None{}, fs, B.Line.body(l)), back, o, run, l, fs, s, lf, b, rest, pend, eof, win)

def decoded.go(inbody: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  match inbody:
    case False{}:
      Went{St{o, NR.head_line(R.is_chrom_line(B.Line.body(l)), NR.tick(run), o, l), Src{b, (lf + 1 : U32)} <> rest, pend, eof, 100n, win, None{}}}
    case True{}:
      slow(back, o, run, l, s, lf, b, rest, pend, eof, win)

def decoded.k(inbody: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +lf: U32, p: D.Bytes & String, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (b, +t) = p
  +l = line(t)
  decoded.go(inbody, back, o, run, l, s, lf, b, rest, pend, eof, win)

def Run.inbody(r: NR.Run) -> NR.Run & Bool:
  match r:
    case NR.Run{n, +i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, i)

def decoded.in(+back: Nat, +o: B.Opts, p: NR.Run & Bool, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, inb) = p
  decoded.k(inb, back, o, run, s, lf, text(b, s, (lf - s : U32)), rest, pend, eof, win)

# The rest of a buffer that holds no complete line goes to pend.
def part.k(+o: B.Opts, run: NR.Run, +back: Nat, p: D.Bytes & D.Bytes, rest: List<&1, Src>, eof: Bool, win: Win) -> Adv:
  (pend, b) = p
  Went{St{o, run, rest, pend, eof, back, win, None{}}}

def part.len(+o: B.Opts, run: NR.Run, +back: Nat, +s: U32, r: D.Bytes & U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (b, +len) = r
  part.k(o, run, back, NR.put_bytes(pend, b, s, (len - s : U32)), rest, eof, win)

def decoded.if(part: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  match part:
    case True{}:
      part.len(o, run, back, s, BY.len(b), rest, pend, eof, win)
    case False{}:
      decoded.in(back, o, Run.inbody(run), s, lf, b, rest, pend, eof, win)

def decoded.lf(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, t: NF.Tb, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  match t:
    case NF.Tb{b, +j, +part, x}:
      decoded.if(part, back, o, run, s, j, b, rest, pend, eof, win)

# The line at s, decoded and handled on its text.
def decoded(+back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  decoded.lf(back, o, run, s, NF.lf(b, s), rest, pend, eof, win)

# ---------------------------------------------------------------------------
# The fast path
# ---------------------------------------------------------------------------

def Run.cur(r: NR.Run) -> NR.Run & String:
  match r:
    case NR.Run{n, i, h, +c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, Maybe.default(&2, String, c, ""))

def Run.same.q(r: NR.Run, b: D.Bytes, q: D.Bytes & Bool) -> NR.Run & (D.Bytes & Bool):
  match r:
    case NR.Run{n, i, h, c, cb0, e, l, f, bk, bn, tl, k, ob, ow, ns, x}:
      (cb, ok) = q
      (NR.Run{n, i, h, c, cb, e, l, f, bk, bn, tl, k, ob, ow, ns, x}, (b, ok))

def Run.same.k(r: NR.Run, p: D.Bytes & (D.Bytes & Bool)) -> NR.Run & (D.Bytes & Bool):
  (b, q) = p
  Run.same.q(r, b, q)

# CHROM (s .. e0-1) is the current run's bytes (fast.run.q also asks for
# a non-empty CHROM: before the first run, cb is empty).
def Run.same(r: NR.Run, b: D.Bytes, +s: U32, +e0: U32) -> NR.Run & (D.Bytes & Bool):
  match r:
    case NR.Run{n, i, h, c, cb, e, l, f, bk, bn, tl, k, ob, ow, ns, x}:
      Run.same.k(NR.Run{n, i, h, c, BY.empty(0n), e, l, f, bk, bn, tl, k, ob, ow, ns, x}, NF.same(b, s, (e0 - s : U32), cb))

def win.ref.q(+c: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, b: D.Bytes, q: D.Bytes & Bool) -> Wo:
  (raw, +eq) = q
  Wo{WKnown{c, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, b, Bool.pick(Wr, eq, WHit{}, WMiss{})}

def win.ref(+c: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, p: D.Bytes & (D.Bytes & Bool)) -> Wo:
  (b, q) = p
  win.ref.q(c, cb, a0, b0, clen, off, offu, rlen, clenu, b, q)

def win.cover(cover: Bool, fits: Bool, +c: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, raw: D.Bytes, +offu: U32, +rlen: U32, +clenu: U32, b: D.Bytes, +rs: U32, +q: U32, +rl: U32) -> Wo:
  match cover fits:
    case False{} _:
      Wo{WKnown{c, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, b, WNeed{}}
    case True{} False{}:
      Wo{WKnown{c, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, b, WMiss{}}
    case True{} True{}:
      win.ref(c, cb, a0, b0, clen, off, offu, rlen, clenu, NF.refeq(b, rs, raw, q, rl))

def win.chrom(ok: Bool, +c: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, raw: D.Bytes, +offu: U32, +rlen: U32, +clenu: U32, b: D.Bytes, +pos: U32, +rs: U32, +rl: U32) -> Wo:
  match ok:
    case False{}:
      Wo{WKnown{c, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, b, WNeed{}}
    case True{}:
      +p = (pos - 1 : U32)
      +end = (p + rl : U32)
      win.cover(U32.is_le(offu, p) && U32.is_le(end, (offu + rlen : U32)), U32.is_le(end, clenu), c, cb, a0, b0, clen, off, raw, offu, rlen, clenu, b, rs, (p - offu : U32), rl)

def win.same.q(+c: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, raw: D.Bytes, +offu: U32, +rlen: U32, +clenu: U32, +pos: U32, +rs: U32, +rl: U32, b: D.Bytes, q: D.Bytes & Bool) -> Wo:
  (cb, +ok) = q
  win.chrom(ok, c, cb, a0, b0, clen, off, raw, offu, rlen, clenu, b, pos, rs, rl)

def win.same(+c: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, raw: D.Bytes, +offu: U32, +rlen: U32, +clenu: U32, +pos: U32, +rs: U32, +rl: U32, p: D.Bytes & (D.Bytes & Bool)) -> Wo:
  (b, q) = p
  win.same.q(c, a0, b0, clen, off, raw, offu, rlen, clenu, pos, rs, rl, b, q)

# The record against the last answer.
def against(w: Win, b: D.Bytes, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32) -> Wo:
  match w:
    case WKnown{+c, cb, +a0, +b0, +clen, +off, raw, +offu, +rlen, +clenu}:
      win.same(c, a0, b0, clen, off, raw, offu, rlen, clenu, pos, rs, rl, NF.same(b, s, (e0 - s : U32), cb))
    case WUnk{c}:
      Wo{WUnk{c}, b, WMiss{}}
    case WNone{}:
      Wo{WNone{}, b, WNeed{}}

def fast.hit(+o: B.Opts, p: NR.Run & Nat, +pos: U32, +s: U32, +lf: U32, b: D.Bytes, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, +n) = p
  done.b(o, NR.fast_done(run, R.Opts.w(o), n, U32.to_nat(pos), b, s, (lf + 1 - s : U32)), (lf + 1 : U32), rest, pend, eof, win)

def fast.need(+o: B.Opts, p: NR.Run & String, +back: Nat, +pos: U32, +rl: U32, b: D.Bytes, +s: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, +c) = p
  +p1 = Nat.sub(U32.to_nat(pos), 1n)
  +a = Nat.sub(p1, margin())
  +req = {P.Req{c, a, Nat.add(Nat.add(p1, U32.to_nat(rl)), ahead())} : P.Req}
  Want{St{o, run, Src{b, s} <> rest, pend, eof, back, win, Some{req}}, req}

def fast.wo(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +lf: U32, +rl: U32, wo: Wo, rest: List<&1, Src>, pend: D.Bytes, eof: Bool) -> Adv:
  match wo:
    case Wo{win, b, WHit{}}:
      fast.hit(o, ticked(run), pos, s, lf, b, rest, pend, eof, win)
    case Wo{win, b, WNeed{}}:
      fast.need(o, Run.cur(run), back, pos, rl, b, s, rest, pend, eof, win)
    case Wo{win, b, WMiss{}}:
      decoded(back, o, run, b, s, rest, pend, eof, win)

def fast.run.if(ok: Bool, +back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, +pos: U32, +lf: U32, +e0: U32, +rs: U32, +rl: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  match ok:
    case True{}:
      fast.wo(back, o, run, s, pos, lf, rl, against(win, b, s, e0, pos, rs, rl), rest, pend, eof)
    case False{}:
      decoded(back, o, run, b, s, rest, pend, eof, win)

def fast.run.q(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +lf: U32, +e0: U32, +rs: U32, +rl: U32, q: D.Bytes & Bool, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (b, ok) = q
  fast.run.if(ok && U32.is_lt(s, e0), back, o, run, b, s, pos, lf, e0, rs, rl, rest, pend, eof, win)

def fast.run(+back: Nat, +o: B.Opts, p: NR.Run & (D.Bytes & Bool), +s: U32, +pos: U32, +lf: U32, +e0: U32, +rs: U32, +rl: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, q) = p
  fast.run.q(back, o, run, s, pos, lf, e0, rs, rl, q, rest, pend, eof, win)

def fast.pre(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, pr: NF.Pr, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  match pr:
    case NF.Pr{b, NF.Pass{+pos, +lf, +e0, +rs, +rl}}:
      fast.run(back, o, Run.same(run, b, s, e0), s, pos, lf, e0, rs, rl, rest, pend, eof, win)
    case NF.Pr{b, NF.Slow{}}:
      decoded(back, o, run, b, s, rest, pend, eof, win)
    case NF.Pr{b, NF.Incomplete{}}:
      decoded(back, o, run, b, s, rest, pend, eof, win)

def body.if(inbody: Bool, +back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  match inbody:
    case True{}:
      fast.pre(back, o, run, s, NF.line(b, s), rest, pend, eof, win)
    case False{}:
      decoded(back, o, run, b, s, rest, pend, eof, win)

def body.k(+back: Nat, +o: B.Opts, p: NR.Run & Bool, b: D.Bytes, +s: U32, rest: List<&1, Src>, pend: D.Bytes, eof: Bool, win: Win) -> Adv:
  (run, inb) = p
  body.if(inb, back, o, run, b, s, rest, pend, eof, win)

# ---------------------------------------------------------------------------
# The machine
# ---------------------------------------------------------------------------

# This step wrote 2^30 bytes or more.
def Run.full(r: NR.Run) -> NR.Run & Bool:
  match r:
    case NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, +ow, ns, x}:
      (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, U32.is_le(1073741824, ow))

def Run.halt(r: NR.Run) -> NR.Run & Bool:
  match r:
    case NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, +x}:
      (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, x)

def advance.src(src: List<&1, Src>, +o: B.Opts, run: NR.Run, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> Adv:
  match src:
    case Nil{}:
      Idle{St{o, run, Nil{}, pend, eof, back, win, asked}}
    case Src{b, +s} <> rest:
      body.k(back, o, Run.inbody(run), b, s, rest, pend, eof, win)

def advance.full(full: Bool, +o: B.Opts, run: NR.Run, src: List<&1, Src>, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> Adv:
  match full:
    case True{}:
      Yield{St{o, run, src, pend, eof, back, win, asked}}
    case False{}:
      advance.src(src, o, run, pend, eof, back, win, asked)

def advance.f(+o: B.Opts, p: NR.Run & Bool, src: List<&1, Src>, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> Adv:
  (run, full) = p
  advance.full(full, o, run, src, pend, eof, back, win, asked)

def advance.h(halt: Bool, +o: B.Opts, run: NR.Run, src: List<&1, Src>, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> Adv:
  match halt:
    case True{}:
      Ended{St{o, run, src, pend, eof, back, win, asked}}
    case False{}:
      advance.f(o, Run.full(run), src, pend, eof, back, win, asked)

def advance.k(+o: B.Opts, p: NR.Run & Bool, src: List<&1, Src>, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> Adv:
  (run, h) = p
  advance.h(h, o, run, src, pend, eof, back, win, asked)

# Handle the next complete line, if any.
def advance(st: St) -> Adv:
  match st:
    case St{+o, run, src, pend, eof, +back, win, asked}:
      advance.k(o, Run.halt(run), src, pend, eof, back, win, asked)

def out.fin(on: D.Bytes & List<&2, B.Note>, st: St, nx: P.Next) -> Step:
  (b, ns) = on
  Step{st, b, ns, nx}

def out.k(p: (D.Bytes & List<&2, B.Note>) & NR.Run, +o: B.Opts, src: List<&1, Src>, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>, nx: P.Next) -> Step:
  (on, run) = p
  out.fin(on, St{o, run, src, pend, eof, back, win, asked}, nx)

def out.left(+o: B.Opts, run: NR.Run, p: List<&1, Src> & U32, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>, nx: P.Next) -> Step:
  (src, +n) = p
  out.k(NR.take(run, n), o, src, pend, eof, back, win, asked, nx)

def left.one(+at: U32, r: D.Bytes & U32) -> Src & U32:
  (b, +len) = r
  (Src{b, at}, (len - at : U32))

def left.cons2(s: Src, +n: U32, q: List<&1, Src> & U32) -> List<&1, Src> & U32:
  (t, +m) = q
  (s <> t, (n + m : U32))

def left.cons(p: Src & U32, q: List<&1, Src> & U32) -> List<&1, Src> & U32:
  (s, +n) = p
  left.cons2(s, n, q)

# The bytes not handled yet in the buffers.
def left(src: List<&1, Src>) -> List<&1, Src> & U32:
  match src:
    case Nil{}:
      (Nil{}, 0)
    case Src{b, +at} <> t:
      left.cons(left.one(at, BY.len(b)), left(t))

# The step ends: what it wrote, and what next.
def out(st: St, nx: P.Next) -> Step:
  match st:
    case St{+o, run, src, pend, eof, +back, win, asked}:
      out.left(o, run, left(src), pend, eof, back, win, asked, nx)

def finish.k(+o: B.Opts, p: NR.Run & Nat, src: List<&1, Src>, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> Step:
  (run, +code) = p
  out(St{o, run, src, pend, eof, back, win, asked}, P.Finish{code})

# The end of the run: the buffer is written (run.bend's finish) and the
# program stops.
def finish(st: St) -> Step:
  match st:
    case St{+o, run, src, pend, eof, +back, win, asked}:
      finish.k(o, NR.finish(run, R.Opts.w(o)), src, pend, eof, back, win, asked)

def idle(st: St) -> Step:
  match st:
    case St{o, run, src, pend, True{}, back, win, asked}:
      finish(St{o, run, src, pend, True{}, back, win, asked})
    case St{o, run, src, pend, False{}, back, win, asked}:
      out(St{o, run, src, pend, False{}, back, win, asked}, P.More{})

# Handle lines until one needs the reference, none is left, or the run stops.
def pump(fuel: Nat, a: Adv) -> Step:
  match fuel a:
    case 0n Went{st}:
      out(st, P.More{})
    case 1n+f Went{st}:
      pump(f, advance(st))
    case _ Want{st, r}:
      out(st, P.Ask{[r]})
    case _ Idle{st}:
      idle(st)
    case _ Ended{st}:
      finish(st)
    case _ Yield{st}:
      out(st, P.Ask{Nil{}})

# More steps than any piece has lines (a piece holds at most 2^31 bytes).
def fuel() -> Nat:
  Nat.mul(4294967295n, 4n)

# ---------------------------------------------------------------------------
# Input
# ---------------------------------------------------------------------------

def feed.join(+o: B.Opts, run: NR.Run, +k: U32, p: D.Bytes & D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  (j, b) = p
  St{o, run, [Src{j, 0}, Src{b, (k + 1 : U32)}], BY.empty(0n), eof, back, win, asked}

def feed.pend(+o: B.Opts, run: NR.Run, p: D.Bytes & D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  (pend, b) = p
  St{o, run, Nil{}, pend, eof, back, win, asked}

def feed.all(+o: B.Opts, run: NR.Run, r: D.Bytes & U32, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  (b, +n) = r
  feed.pend(o, run, NR.put_bytes(pend, b, 0, n), eof, back, win, asked)

def feed.lf(none: Bool, +o: B.Opts, run: NR.Run, b: D.Bytes, +k: U32, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  match none:
    case True{}:
      feed.all(o, run, BY.len(b), pend, eof, back, win, asked)
    case False{}:
      feed.join(o, run, k, NR.put_bytes(pend, b, 0, (k + 1 : U32)), eof, back, win, asked)

def feed.find(+o: B.Opts, run: NR.Run, t: NF.Tb, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  match t:
    case NF.Tb{b, +k, +none, x}:
      feed.lf(none, o, run, b, k, pend, eof, back, win, asked)

def feed.if(empty: Bool, +o: B.Opts, run: NR.Run, src: List<&1, Src>, b: D.Bytes, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  match empty:
    case True{}:
      St{o, run, List.append(&1, Src, src, [Src{b, 0}]), pend, eof, back, win, asked}
    case False{}:
      feed.find(o, run, NF.lf(b, 0), pend, eof, back, win, asked)

def feed.k(+o: B.Opts, run: NR.Run, src: List<&1, Src>, b: D.Bytes, r: D.Bytes & U32, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  (pend, +n) = r
  feed.if(U32.is_zero(n), o, run, src, b, pend, eof, back, win, asked)

def feed.room(+o: B.Opts, run: NR.Run, src: List<&1, Src>, r: D.Bytes & U32, pend: D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  (b, +n) = r
  feed.k(o, NR.reserve(run, n), src, b, BY.len(pend), eof, back, win, asked)

# A piece of the VCF file: its lines are read in place; the end of a line
# left from the last piece is joined with this piece's first line.
def feed(st: St, b: D.Bytes) -> St:
  match st:
    case St{+o, run, src, pend, eof, +back, win, asked}:
      feed.room(o, run, src, BY.len(b), pend, eof, back, win, asked)

def feed_eof.if(empty: Bool, +o: B.Opts, run: NR.Run, src: List<&1, Src>, pend: D.Bytes, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  match empty:
    case True{}:
      St{o, run, src, pend, True{}, back, win, asked}
    case False{}:
      St{o, run, List.append(&1, Src, src, [Src{NR.put_str(pend, "\n"), 0}]), BY.empty(0n), True{}, back, win, asked}

def feed_eof.k(+o: B.Opts, run: NR.Run, src: List<&1, Src>, r: D.Bytes & U32, +back: Nat, win: Win, asked: Maybe<&2, P.Req>) -> St:
  (pend, +n) = r
  feed_eof.if(U32.is_zero(n), o, run, src, pend, back, win, asked)

# The end of the file: what is left after the last LF is the last line, given
# an LF (its text as B.Text.last has it: the bytes, then LF).
def feed_eof(st: St) -> St:
  match st:
    case St{+o, run, src, pend, eof, +back, win, asked}:
      feed_eof.k(o, run, src, BY.len(pend), back, win, asked)

def set_win.of(asked: Maybe<&2, P.Req>, win: Win, ans: Maybe<&1, P.Ans>) -> Win:
  match asked:
    case None{}:
      win
    case Some{r}:
      win_of(Some{r}, ans)

# The answer to the read asked last, kept (after an empty Ask, the last
# answer stays).
def set_win(st: St, ans: Maybe<&1, P.Ans>) -> St:
  match st:
    case St{o, run, src, pend, eof, back, win, asked}:
      St{o, run, src, pend, eof, back, set_win.of(asked, win, ans), None{}}

# The first answer (the machine asks one read at a time).
def first(as: List<&1, P.Ans>) -> Maybe<&1, P.Ans>:
  match as:
    case Nil{}:
      None{}
    case a <> t:
      Some{a}

# One step of the program.
def step(st: St, i: P.In) -> Step:
  match i:
    case P.Chunk{b}:
      pump(fuel(), advance(feed(st, b)))
    case P.Eof{}:
      pump(fuel(), advance(feed_eof(st)))
    case P.Ref{as}:
      pump(fuel(), advance(set_win(st, first(as))))
