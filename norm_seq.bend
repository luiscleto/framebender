import Base
import ./types.bend as B
import ./protocol.bend as P
import ./run.bend as R
import ./norm_line.bend as J
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./norm_split.bend as NS
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F

# framebender: the program (code, not spec). MACHINE.bend states what it must
# do; the law reaches the code through Norm.start and Norm.step.
#
# The input arrives as packed buffers (bytes_enc.bend's enc of each piece).
# Lines are read in place. A record in the current CHROM run that passes the
# fast path's tests (norm_fast.bend, and the CHROM and REF tests here) is
# written as it came: its bytes go to the output buffer, nothing is decoded.
# Every other line is decoded (its text, as bytes_enc.bend's text gives it)
# and handled by the String code (norm_line.bend: J.judge_fs, J.fast).
#
# Sizes. The byte mode keeps every buffer well within 2^31 bytes: a line of
# more than 2^28 bytes, or an output buffer past 2^29 bytes, switches the run
# to the String mode for the rest of the file (run.bend's own state, its
# output written at most 2^30 bytes a step), and an unfinished line past 2^28
# bytes is kept as text. A reference read asks for at most 2^31 letters; a
# wider window is asked for in parts. notes/bytes.md has the design.

# ---------------------------------------------------------------------------
# The state
# ---------------------------------------------------------------------------

# Input not handled yet: a buffer whose lines from at on are not handled
# (SB), or one complete line's text before its LF (SL), or the records of a
# line split by -m, from at on (SP: each is handled as a line with the split
# line's number, which was counted once when it was split), or one such
# record as its exact line (SR: split on its text; the String mode reads it).
type Src is Type:
  SB{b: D.Bytes, at: U32}
  SL{p: String}
  SP{b: D.Bytes, at: U32}
  SR{l: B.Line}

# The end of a line not yet complete: bytes, or (past 2^28 bytes) text.
type Pd is Type:
  PB{b: D.Bytes}
  PS{s: String}

# The last reference answer, kept to answer later reads from it.
#   WUnk: contig c is not in the reference.
#   WKnown: the answer to the read of c from a up to b: c's length clen, and
#     its letters from off (as P.Known); cb: c's bytes; offu, rlen, clenu:
#     off, raw's length and clen as U32 (clenu 0 when they do not fit).
#   WStr: the same, read in parts and decoded (raw: its letters as text).
type Win is Type:
  WNone{}
  WUnk{c: String}
  WKnown{c: String, cb: D.Bytes, a: Nat, b: Nat, clen: Nat, off: Nat, raw: D.Bytes, offu: U32, rlen: U32, clenu: U32}
  WStr{c: String, a: Nat, b: Nat, clen: Nat, off: Nat, raw: String}

# The run: on bytes (norm_run.bend), or in the String mode: run.bend's state
# s (its out kept empty), the output not yet handed out (qs, newest first,
# ql bytes in all), and the exit code once the run has finished.
type Md is Type:
  MB{r: NR.Run}
  MS{s: R.RunSt, qs: List<&2, String>, ql: Nat, code: Maybe<&2, Nat>}

# The machine's state: the options; the run; the input not handled yet; the
# end of a line not yet complete (pend); whether the file ended; how far back
# the next reference read for the waiting line starts; the last reference
# answer; the reads asked last; whether the fast path already asked a read
# for the waiting line.
type St is Type:
  St{o: B.Opts, md: Md, src: List<&1, Src>, pend: Pd, eof: Bool, back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, fneed: Bool, dfs: B.Defs}

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
#   Went: a line was handled (or the input or the run changed form).
#   Want: the line needs reference reads.
#   Idle: no complete line is left.
#   Ended: the run has stopped, or finished writing.
#   Yield: this step wrote 2^30 bytes or more; the step ends (so that an
#     output buffer stays within 2^31 bytes) and the next one goes on.
type Adv is Type:
  Went{st: St}
  Want{st: St, reqs: List<&2, P.Req>}
  Idle{st: St}
  Ended{st: St}
  Yield{st: St}

# The input the line paths do not touch; the header's definitions (-m); hold:
# the line is a record of a split line (SP), whose count was taken when the
# line was split (the run was unticked before it, so its own tick restores
# the count).
type Cx is Type:
  Cx{rest: List<&1, Src>, pend: Pd, eof: Bool, dfs: B.Defs, hold: Bool}

# A read answered from the last answer (Some), or not (None); clen: the
# contig's length (for grow).
type Sv is Type:
  Sv{win: Win, ans: Maybe<&2, J.Ans>, clen: Nat}

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
#   answer does not hold the window, reqs ask for it.
type Sx is Type:
  SAgain{win: Win, back: Nat}
  SDone{win: Win, f: J.Fast, back: Nat}
  SMiss{win: Win, reqs: List<&2, P.Req>, back: Nat}

# A record's verdict on its text: J.fast's (Same or a result), or the reads
# it needs.
type Vd is Type:
  VRes{win: Win, r: B.Res}
  VSame{win: Win}
  VWant{win: Win, reqs: List<&2, P.Req>, back: Nat}

# ---------------------------------------------------------------------------
# The machine
# ---------------------------------------------------------------------------

# The byte run's state: stopped, this step wrote 2^30 bytes or more, the
# output buffer holds 2^29 bytes or more.
type Rs is Data:
  Rs{halt: Bool, full: Bool, big: Bool}

# The first (at most) w characters of s, and the rest.
type Cut2 is Data:
  Cut2{now: String, later: String}

# The result for one body line through a reference answer (norm_line.bend).
def judge_in(a: Maybe<&2, J.Ans>, +body: String) -> Maybe<&2, B.Res>:
  J.judge_in(a, body)

def start.of(m: Maybe<&2, B.Cfg>) -> Begin:
  match m:
    case None{}:
      Usage{}
    case Some{B.Cfg{o, r, v}}:
      Begin{St{o, MB{NR.start()}, Nil{}, PB{BY.empty(0n)}, False{}, 0n, WNone{}, None{}, False{}, B.Defs{Nil{}, Nil{}}}, r, v}

# The command line after the program's name.
def start(argv: List<&2, String>) -> Begin:
  start.of(B.Args.parse(argv))

# How many letters a reference read asks for past what the line needs, so
# that the next lines are answered from it, and before it. With margin(), a
# read of ahead() + margin() + 1 letters fits a block of 4 MiB, as a VCF
# piece does (notes/memory.md).
def ahead() -> Nat:
  4128767n

def margin() -> Nat:
  65536n

# The most bytes the String mode hands out in one step.
def lim() -> Nat:
  1073741824n

# Size checks are made on words (U32), which the checker evaluates natively
# and lawful-words relates to Nat; a big Nat constant could not be related
# to anything in the proofs (notes/bytes_proofs.md).

# s has at most w characters (counted down on a word).
def len_le.go(s: String, z: Bool, +w: U32) -> Bool:
  match s z:
    case SNil{} _:
      True{}
    case SCon{h, t} True{}:
      False{}
    case SCon{h, t} False{}:
      len_le.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32))

def len_le(s: String, +w: U32) -> Bool:
  len_le.go(s, U32.is_zero(w), w)

def take_w.cons(+h: Char, c: Cut2) -> Cut2:
  match c:
    case Cut2{n, l}:
      Cut2{SCon{h, n}, l}

def take_w.go(s: String, z: Bool, +w: U32) -> Cut2:
  match s z:
    case SNil{} _:
      Cut2{"", ""}
    case SCon{h, t} True{}:
      Cut2{"", SCon{h, t}}
    case SCon{+h, t} False{}:
      take_w.cons(h, take_w.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32)))

def take_w(s: String, +w: U32) -> Cut2:
  take_w.go(s, U32.is_zero(w), w)

# n fits a word below 2^31 (no wrap: the word reads back as n).
def fits31(+n: Nat) -> Bool:
  Nat.is_eq(U32.to_nat(U32.from_nat(n)), n) && U32.is_lt(U32.from_nat(n), 2147483648)

# n is at most 2^31 (E.le31: the size of one read).
def le31(+n: Nat) -> Bool:
  Nat.is_eq(U32.to_nat(U32.from_nat(n)), n) && U32.is_le(U32.from_nat(n), 2147483648)

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

def text.all(r: D.Bytes & String) -> String:
  (b, t) = r
  t

# All of a buffer's bytes as text.
def text_of(b: D.Bytes) -> String:
  D.Bytes{+n, buf} = b
  text.all(text(D.Bytes{n, buf}, 0, n))

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

# ---------------------------------------------------------------------------
# Reference reads
# ---------------------------------------------------------------------------

# The reads for letters a .. b of contig c: one read if it has at most 2^31
# letters (le31, E.reqs_ok), else the two halves, each read the same way.
# fuel: b - a, more than the halvings. No big constant appears, so proofs
# never meet a closed big Nat (notes/bytes_proofs.md).
def parts.go(fuel: Nat, one: Bool, +c: String, +a: Nat, +b: Nat) -> List<&2, P.Req>:
  match fuel one:
    case _ True{}:
      [P.Req{c, a, b}]
    case 0n False{}:
      [P.Req{c, a, b}]
    case 1n+(+f) False{}:
      +m = Nat.add(a, Nat.div(Nat.sub(b, a), 2n))
      List.append(&2, P.Req, parts.go(f, le31(Nat.sub(m, a)), c, a, m), parts.go(f, le31(Nat.sub(b, m)), c, m, b))

def parts(+c: String, +a: Nat, +b: Nat) -> List<&2, P.Req>:
  parts.go(Nat.sub(b, a), le31(Nat.sub(b, a)), c, a, b)

# The reads asked when the last answer does not hold a .. e: from margin()
# letters earlier (records a little out of order, or a window grown back,
# are then answered from it), up to ahead() letters on, in one read; if that
# is more than one read can hold, just a .. e.
def Req.of.k(one: Bool, +c: String, +a: Nat, +e: Nat, +a2: Nat, +e2: Nat) -> List<&2, P.Req>:
  match one:
    case True{}:
      [P.Req{c, a2, e2}]
    case False{}:
      parts(c, a, e)

def Req.of(+c: String, +a: Nat, +e: Nat) -> List<&2, P.Req>:
  +a2 = Nat.sub(a, margin())
  +e2 = Nat.max(e, Nat.add(a, ahead()))
  Req.of.k(le31(Nat.sub(e2, a2)), c, a, e, a2, e2)

def serve.slice(+c: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, +a2: Nat, r: D.Bytes & List<&2, U32>) -> Sv:
  (raw, xs) = r
  Sv{WKnown{c, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, Some{J.Known{clen, a2, chars(xs)}}, clen}

def serve.known(hit: Bool, w: Win, +a: Nat, +b: Nat) -> Sv:
  match hit w:
    case True{} WKnown{+c, cb, +a0, +b0, +clen, +off, raw, +offu, +rlen, +clenu}:
      +a2 = Nat.min(a, clen)
      +n = Nat.sub(Nat.min(b, clen), a2)
      serve.slice(c, cb, a0, b0, clen, off, offu, rlen, clenu, a2, BY.to_list(raw, U32.from_nat(Nat.sub(a2, off)), U32.from_nat(n)))
    case _ w:
      Sv{w, None{}, 0n}

def serve.unk(hit: Bool, +c0: String) -> Sv:
  match hit:
    case True{}:
      Sv{WUnk{c0}, Some{J.Unknown{}}, 0n}
    case False{}:
      Sv{WUnk{c0}, None{}, 0n}

def serve.str(hit: Bool, +c0: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +raw: String, +a: Nat, +b: Nat) -> Sv:
  match hit:
    case True{}:
      +a2 = Nat.min(a, clen)
      Sv{WStr{c0, a0, b0, clen, off, raw}, Some{J.Known{clen, a2, String.take(String.drop(raw, Nat.sub(a2, off)), Nat.sub(Nat.min(b, clen), a2))}}, clen}
    case False{}:
      Sv{WStr{c0, a0, b0, clen, off, raw}, None{}, 0n}

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
    case WStr{+c0, +a0, +b0, +clen, +off, +raw}:
      serve.str(String.eq(c0, c) && Nat.is_le(a0, a) && Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen)), c0, a0, b0, clen, off, raw, a, b)

def win_of.k(+c: String, +a: Nat, +b: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32) -> Win:
  (raw, +rl) = r
  +fits = fits31(off) && fits31(clen)
  WKnown{c, NR.of_str(c), a, b, clen, off, raw, U32.from_nat(off), rl, Bool.pick(U32, fits, U32.from_nat(clen), 0)}

# The letters of the answers after the first, decoded and joined.
def raws(as: List<&1, P.Ans>) -> String:
  match as:
    case Nil{}:
      ""
    case P.Known{n, o, raw} <> t:
      text_of(raw) ++ raws(t)
    case P.Unknown{} <> t:
      raws(t)

def last_b(rs: List<&2, P.Req>, +b: Nat) -> Nat:
  match rs:
    case Nil{}:
      b
    case P.Req{c, a, b2} <> t:
      last_b(t, b2)

# Answers read in parts: one window, decoded.
def win_parts(+c: String, +a: Nat, +b: Nat, as: List<&1, P.Ans>) -> Win:
  match as:
    case P.Known{+clen, +off, raw} <> t:
      WStr{c, a, b, clen, off, text_of(raw) ++ raws(t)}
    case P.Unknown{} <> t:
      WUnk{c}
    case Nil{}:
      WNone{}

def win_of.single(+c: String, +a: Nat, +b: Nat, as: List<&1, P.Ans>) -> Win:
  match as:
    case P.Known{+clen, +off, raw} <> t:
      win_of.k(c, a, b, clen, off, BY.len(raw))
    case P.Unknown{} <> t:
      WUnk{c}
    case Nil{}:
      WNone{}

def win_of.one(t: List<&2, P.Req>, +c: String, +a: Nat, +b: Nat, as: List<&1, P.Ans>) -> Win:
  match t:
    case Nil{}:
      win_of.single(c, a, b, as)
    case r <> t2:
      win_parts(c, a, last_b(r <> t2, b), as)

# The answers to the reads asked last, kept.
def win_of(rs: List<&2, P.Req>, as: List<&1, P.Ans>) -> Win:
  match rs:
    case Nil{}:
      WNone{}
    case P.Req{+c, +a, +b} <> t:
      win_of.one(t, c, a, b, as)

# How far back the next window starts: twice as far, or (once the window is
# as long as the contig) back to the contig's first letter.
def grow(+clen: Nat, +back: Nat, +pos: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(clen, back) && Bool.not(Nat.is_eq(clen, 0n)), pos, Nat.add(Nat.mul(back, 2n), 1n))

def slow.f(+back: Nat, +clen: Nat, +pos: Nat, win: Win, f: J.Fast) -> Sx:
  match f:
    case J.Other{None{}}:
      SAgain{win, grow(clen, back, pos)}
    case f:
      SDone{win, f, back}

def slow.sv(+back: Nat, +reqs: List<&2, P.Req>, +fs: List<&2, String>, +body: String, sv: Sv) -> Sx:
  match sv:
    case Sv{win, None{}, k}:
      SMiss{win, reqs, back}
    case Sv{win, Some{ans}, +clen}:
      slow.f(back, clen, B.Rec.pos(fs), win, J.fast(Some{ans}, fs, body))

# The reads when the last answer does not hold the window: on the line's
# first try (back is still 0), Req.of's window; once the window has grown,
# the contig from its first letter to the end of REF, which holds every
# later try (so a line asks at most twice on the slow path).
def slow.reqs(first: Bool, +c: String, +a: Nat, +e: Nat) -> List<&2, P.Req>:
  match first:
    case True{}:
      Req.of(c, a, e)
    case False{}:
      parts(c, 0n, e)

# One try, with the window back letters before POS.
def slow.try(win: Win, +back: Nat, +fs: List<&2, String>, +body: String) -> Sx:
  +p = Nat.sub(B.Rec.pos(fs), 1n)
  +c = B.Rec.field(fs, 0n)
  +a = Nat.sub(p, back)
  +e = Nat.add(p, String.length(B.Rec.field(fs, 3n)))
  slow.sv(back, slow.reqs(Nat.is_eq(back, 0n), c, a, e), fs, body, serve(win, c, a, e))

def slow.go(fuel: Nat, x: Sx, +fs: List<&2, String>, +body: String) -> Sx:
  match fuel x:
    case 1n+k SAgain{win, +back}:
      slow.go(k, slow.try(win, back, fs, body), fs, body)
    case _ x:
      x

# Out of tries (or no answer): read the contig from its first letter and
# try once more from there (back = POS), which decides (the line's Wants
# stay bounded; notes/bytes_proofs_budget.md).
def vd.x(x: Sx, +fs: List<&2, String>) -> Vd:
  match x:
    case SDone{win, J.Same{}, back}:
      VSame{win}
    case SDone{win, J.Other{Some{r}}, back}:
      VRes{win, r}
    case SMiss{win, +reqs, +back}:
      VWant{win, reqs, back}
    case SDone{win, J.Other{None{}}, back}:
      VWant{win, parts(B.Rec.field(fs, 0n), 0n, Nat.add(B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)))), B.Rec.pos(fs)}
    case SAgain{win, back}:
      VWant{win, parts(B.Rec.field(fs, 0n), 0n, Nat.add(B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)))), B.Rec.pos(fs)}

def vd.m(m: Maybe<&2, B.Res>, +back: Nat, win: Win, +fs: List<&2, String>, +body: String) -> Vd:
  match m:
    case Some{r}:
      VRes{win, r}
    case None{}:
      vd.x(slow.go(64n, SAgain{win, back}, fs, body), fs)

# A body line judged on its text (fs: J.pfs of its body), the window grown
# from back letters before POS.
def verdict(+back: Nat, win: Win, +fs: List<&2, String>, +body: String) -> Vd:
  vd.m(J.judge_fs(None{}, fs, body), back, win, fs, body)

def at_of(+n: Nat, +fs: List<&2, String>) -> B.At:
  B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}

# ---------------------------------------------------------------------------
# The String mode: one line, as run.bend handles it
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Splitting (-m): the context's header definitions, the records written
# ---------------------------------------------------------------------------

# B.Defs.line, its prefix matched first: B.Defs.line's Bool.pick takes both
# branches as arguments, so a run would parse every header line twice
# (Hdr.tag), the #CHROM line too, here only a definition, once
# (proof_b_defs_line.bend's line_eq: the two are equal).
def defs.fmt(fmt: Bool, +d: B.Defs, +body: String) -> B.Defs:
  match fmt:
    case True{}:
      B.Defs.add_fmt(B.Hdr.tag(String.drop(body, 10n)), d)
    case False{}:
      d

def defs.info(info: Bool, +d: B.Defs, +body: String) -> B.Defs:
  match info:
    case True{}:
      B.Defs.add_info(B.Hdr.tag(String.drop(body, 8n)), d)
    case False{}:
      defs.fmt(String.starts_with(body, "##FORMAT=<"), d, body)

def defs.line(+d: B.Defs, +body: String) -> B.Defs:
  defs.info(String.starts_with(body, "##INFO=<"), d, body)

# A header line's definition added (B.Defs.line, as defs.line; lines before
# #CHROM).
def Cx.line(cx: Cx, +body: String) -> Cx:
  match cx:
    case Cx{rest, pend, eof, +dfs, hold}:
      Cx{rest, pend, eof, defs.line(dfs, body), hold}

# What B.Rec.parts says of a body line.
def Cx.parts(cx: Cx, +o: B.Opts, +body: String) -> Cx & B.Parts:
  match cx:
    case Cx{rest, pend, eof, +dfs, hold}:
      (Cx{rest, pend, eof, dfs, hold}, B.Rec.parts(dfs, o, body))

# The records of a split line, as exact lines (SR), before the rest.
def recs_src(ps: List<&2, String>, +term: String, rest: List<&1, Src>) -> List<&1, Src>:
  match ps:
    case Nil{}:
      rest
    case +p <> t:
      SR{B.Line{p, term}} <> recs_src(t, term, rest)

def Cx.push(cx: Cx, ps: List<&2, String>, +term: String) -> Cx:
  match cx:
    case Cx{rest, pend, eof, dfs, hold}:
      Cx{recs_src(ps, term, rest), pend, eof, dfs, hold}

def recs_text(ps: List<&2, String>, +term: String) -> String:
  match ps:
    case Nil{}:
      ""
    case p <> t:
      p ++ term ++ recs_text(t, term)

# The outcome stops the run: MALFORMED, UNKNOWN_CHROM, a problem under -c e
# (LAWS.bend's stops).
def stops(r: B.Res, strict: Bool) -> Bool:
  match r:
    case B.Res{B.Broken{}, k, t, x}:
      True{}
    case B.Res{B.NoContig{}, k, t, x}:
      True{}
    case B.Res{B.Problem{c}, k, t, x}:
      strict
    case _:
      False{}

def unsplit.res(+c: B.Code, +strict: Bool, +fs: List<&2, String>, +body: String, +r: B.Res) -> B.Res:
  Bool.pick(B.Res, stops(r, strict), r, B.Res{B.Problem{c}, B.Rec.pos(fs), body, False{}})

# A line -m cannot split (code c): the whole line's outcome when it stops the
# run, else the problem c (LAWS.bend's unsplit_in).
def vd.unsplit(+c: B.Code, +strict: Bool, +fs: List<&2, String>, +body: String, v: Vd) -> Vd:
  match v:
    case VRes{win, +r}:
      VRes{win, unsplit.res(c, strict, fs, body, r)}
    case VSame{win}:
      VRes{win, B.Res{B.Problem{c}, B.Rec.pos(fs), body, False{}}}
    case VWant{win, reqs, back}:
      VWant{win, reqs, back}

# A line for the String mode: its text before its LF (read as B.Text.line
# reads it), or a record of a split line as its exact line (SR).
type Ls is Data:
  LsT{p: String}
  LsR{l: B.Line}

def Ls.line(+ls: Ls) -> B.Line:
  match ls:
    case LsT{+p}:
      line(p)
    case LsR{+l}:
      l

def ms.out(s: R.RunSt, qs: List<&2, String>, +ql: Nat) -> Md:
  match s:
    case R.RunSt{n, i, h, c, e, l, b, k, +o, ns, x}:
      MS{R.RunSt{n, i, h, c, e, l, b, k, "", ns, x}, o <> qs, Nat.add(ql, String.length(o)), None{}}

def ms.done(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, cx: Cx, win: Win) -> Adv:
  match cx:
    case Cx{rest, pend, eof, dfs, hold}:
      Went{St{o, ms.out(s, qs, ql), rest, pend, eof, 0n, win, None{}, False{}, dfs}}

# The line is asked again later: a text as SL (handled without untick, from
# the run as it is here), a record as SR (unticked again then: the count it
# was unticked by is given back).
def ms.want.k(+ls: Ls, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, rest: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, +reqs: List<&2, P.Req>, dfs: B.Defs) -> Adv:
  match ls:
    case LsT{+p}:
      Want{St{o, MS{s, qs, ql, None{}}, SL{p} <> rest, pend, eof, back, win, Some{reqs}, False{}, dfs}, reqs}
    case LsR{+l}:
      Want{St{o, MS{R.tick(s), qs, ql, None{}}, SR{l} <> rest, pend, eof, back, win, Some{reqs}, False{}, dfs}, reqs}

def ms.want(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, cx: Cx, win: Win, +reqs: List<&2, P.Req>, +back: Nat) -> Adv:
  match cx:
    case Cx{rest, pend, eof, dfs, hold}:
      ms.want.k(ls, o, s, qs, ql, rest, pend, eof, back, win, reqs, dfs)

# A body line in the String mode: run.bend's body_line with the verdict.
def ms.body(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, +l: B.Line, +fs: List<&2, String>, cx: Cx, v: Vd) -> Adv:
  match v:
    case VRes{win, r}:
      +s1 = R.tick(s)
      ms.done(o, R.body_line(r, s1, o, l, at_of(R.RunSt.n(s1), fs), B.Rec.pos(fs)), qs, ql, cx, win)
    case VSame{win}:
      +s1 = R.tick(s)
      ms.done(o, R.body_line(B.Res{B.Normalized{}, B.Rec.pos(fs), B.Line.body(l), False{}}, s1, o, l, at_of(R.RunSt.n(s1), fs), B.Rec.pos(fs)), qs, ql, cx, win)
    case VWant{win, +reqs, +back}:
      ms.want(o, s, qs, ql, ls, cx, win, reqs, back)

def ms.parts.k(pt: B.Parts, cx: Cx, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, +l: B.Line, +back: Nat, win: Win) -> Adv:
  match pt:
    case B.Whole{}:
      +fs = J.pfs(B.Line.body(l))
      ms.body(o, s, qs, ql, ls, l, fs, cx, verdict(back, win, fs, B.Line.body(l)))
    case B.Pieces{ps}:
      ms.done(o, R.tick(s), qs, ql, Cx.push(cx, ps, B.Line.term(l)), win)
    case B.Unsplit{+c}:
      +fs = J.pfs(B.Line.body(l))
      ms.body(o, s, qs, ql, ls, l, fs, cx, vd.unsplit(c, R.Opts.strict(o), fs, B.Line.body(l), verdict(back, win, fs, B.Line.body(l))))

def ms.parts(r: Cx & B.Parts, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, +l: B.Line, +back: Nat, win: Win) -> Adv:
  (cx, pt) = r
  ms.parts.k(pt, cx, o, s, qs, ql, ls, l, back, win)

# A body line in the String mode: with -m, split first (B.Rec.parts).
def ms.split(split: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, +l: B.Line, +back: Nat, cx: Cx, win: Win) -> Adv:
  match split:
    case False{}:
      +fs = J.pfs(B.Line.body(l))
      ms.body(o, s, qs, ql, ls, l, fs, cx, verdict(back, win, fs, B.Line.body(l)))
    case True{}:
      ms.parts(Cx.parts(cx, o, B.Line.body(l)), o, s, qs, ql, ls, l, back, win)

def ms.line.k(inbody: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, +l: B.Line, +back: Nat, cx: Cx, win: Win) -> Adv:
  match inbody:
    case False{}:
      ms.done(o, R.head_line(R.is_chrom_line(B.Line.body(l)), R.tick(s), o, l), qs, ql, Cx.line(cx, B.Line.body(l)), win)
    case True{}:
      ms.split(R.Opts.split(o), o, s, qs, ql, ls, l, back, cx, win)

def ms.line.go(inbody: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, +back: Nat, cx: Cx, win: Win) -> Adv:
  +l = Ls.line(ls)
  ms.line.k(inbody, o, s, qs, ql, ls, l, back, cx, win)

# One line (its text p, before its LF) in the String mode.
def ms.line(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +ls: Ls, +back: Nat, cx: Cx, win: Win) -> Adv:
  match s:
    case R.RunSt{n, +i, h, c, e, l, b, k, out, ns, x}:
      ms.line.go(i, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}, qs, ql, ls, back, cx, win)

# ---------------------------------------------------------------------------
# The byte mode: lines decoded (header lines and the slow path)
# ---------------------------------------------------------------------------

# The rest of a buffer, as it was: plain lines, or the records of a split
# line (hold).
def Src.of(hold: Bool, b: D.Bytes, +at: U32) -> Src:
  match hold:
    case True{}:
      SP{b, at}
    case False{}:
      SB{b, at}

# A record of a split line not handled now (it is asked again later, from
# SP, which unticks again): the count it was unticked by is given back.
def retick(hold: Bool, run: NR.Run) -> NR.Run:
  match hold:
    case True{}:
      NR.tick(run)
    case False{}:
      run

# The line is done: the input moves past it.
def done.b(+o: B.Opts, p: NR.Run & D.Bytes, +at: U32, cx: Cx, win: Win) -> Adv:
  (run, b) = p
  match cx:
    case Cx{rest, pend, eof, dfs, +hold}:
      Went{St{o, MB{run}, Src.of(hold, b, at) <> rest, pend, eof, 0n, win, None{}, False{}, dfs}}

def ticked(run: NR.Run) -> NR.Run & Nat:
  NR.Run.n(NR.tick(run))

def Run.n(r: NR.Run) -> NR.Run & Nat:
  NR.Run.n(r)

# The byte run as the String mode's state (its out: what this step wrote).
def to_ms(r: NR.Run) -> Md:
  ms.out(NR.to_spec(r), Nil{}, 0n)

# The run switches to the String mode; the line at s is handled there next.
def to_str(+o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, +back: Nat, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match cx:
    case Cx{rest, pend, eof, dfs, +hold}:
      Went{St{o, to_ms(retick(hold, run)), Src.of(hold, b, s) <> rest, pend, eof, back, win, None{}, fneed, dfs}}

def want.b(+o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, +back: Nat, cx: Cx, win: Win, +reqs: List<&2, P.Req>, +fneed: Bool) -> Adv:
  match cx:
    case Cx{rest, pend, eof, dfs, +hold}:
      Want{St{o, MB{retick(hold, run)}, Src.of(hold, b, s) <> rest, pend, eof, back, win, Some{reqs}, fneed, dfs}, reqs}

def same_done(+o: B.Opts, p: NR.Run & Nat, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win) -> Adv:
  (run, +n) = p
  done.b(o, NR.same_done(run, o, at_of(n, fs), B.Rec.pos(fs), b, s, (lf + 1 - s : U32)), (lf + 1 : U32), cx, win)

def body_done(r: B.Res, +o: B.Opts, p: NR.Run & Nat, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win) -> Adv:
  (run, +n) = p
  done.b(o, NR.body_line(r, run, o, l, at_of(n, fs), B.Rec.pos(fs), b, s, (lf + 1 - s : U32)), (lf + 1 : U32), cx, win)

# A result's new text fits room more bytes of the output buffer (a line
# kept as it came adds its own bytes, at most 2^28).
def res_fits(r: B.Res, +l: B.Line, +room: U32) -> Bool:
  match r:
    case B.Res{B.Normalized{}, k, +t, st}:
      Bool.pick(Bool, String.eq(t, B.Line.body(l)), True{}, len_le(B.Line.text(B.Line{t, B.Line.term(l)}), room))
    case _:
      True{}

def body.fits(fits: Bool, r: B.Res, +o: B.Opts, run: NR.Run, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, +back: Nat, cx: Cx, win: Win) -> Adv:
  match fits:
    case True{}:
      body_done(r, o, ticked(run), l, fs, s, lf, b, cx, win)
    case False{}:
      to_str(o, run, b, s, back, cx, win, False{})

def Run.oblen(r: NR.Run) -> NR.Run & U32:
  match r:
    case NR.Run{n, i, h, c, cb, e, l, f, bk, bn, tl, k, ob, ow, ns, x}:
      D.Bytes{+len, buf} = ob
      (NR.Run{n, i, h, c, cb, e, l, f, bk, bn, tl, k, D.Bytes{len, buf}, ow, ns, x}, len)

# (The output buffer holds less than 2^29 bytes here, Rs, so 2^30 - obl does
# not wrap.)
def body.res(+r: B.Res, +o: B.Opts, p: NR.Run & U32, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, +back: Nat, cx: Cx, win: Win) -> Adv:
  (run, +ol) = p
  body.fits(res_fits(r, l, (1073741824 - ol : U32)), r, o, run, l, fs, s, lf, b, back, cx, win)

def slow.vd(+o: B.Opts, run: NR.Run, +l: B.Line, +fs: List<&2, String>, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, +fneed: Bool, +back0: Nat, v: Vd) -> Adv:
  match v:
    case VRes{win, r}:
      body.res(r, o, Run.oblen(run), l, fs, s, lf, b, back0, cx, win)
    case VSame{win}:
      same_done(o, ticked(run), fs, s, lf, b, cx, win)
    case VWant{win, +reqs, +back}:
      want.b(o, run, b, s, back, cx, win, reqs, fneed)

# A body line the fast path did not take: judged on its text.
def slow.whole(+back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  +fs = J.pfs(B.Line.body(l))
  slow.vd(o, run, l, fs, s, lf, b, cx, fneed, back, verdict(back, win, fs, B.Line.body(l)))

# A split line's records (their bytes, each with its terminator): the line is
# counted once, and its records are read next, before the rest of the input.
def inject(+o: B.Opts, run: NR.Run, b: D.Bytes, +lf: U32, recs: D.Bytes, cx: Cx, win: Win) -> Adv:
  match cx:
    case Cx{rest, pend, eof, dfs, +hold}:
      Went{St{o, MB{NR.tick(run)}, SP{recs, 0} <> Src.of(hold, b, (lf + 1 : U32)) <> rest, pend, eof, 0n, win, None{}, False{}, dfs}}

# The same for records split on their text (the String path): as exact lines
# (SR), which the String mode reads.
def inject.r(+o: B.Opts, run: NR.Run, b: D.Bytes, +lf: U32, ps: List<&2, String>, +term: String, cx: Cx, win: Win) -> Adv:
  match cx:
    case Cx{rest, pend, eof, dfs, +hold}:
      Went{St{o, MB{NR.tick(run)}, recs_src(ps, term, Src.of(hold, b, (lf + 1 : U32)) <> rest), pend, eof, 0n, win, None{}, False{}, dfs}}

def slow.parts.k(pt: B.Parts, cx: Cx, +back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, win: Win, +fneed: Bool) -> Adv:
  match pt:
    case B.Whole{}:
      slow.whole(back, o, run, l, s, lf, b, cx, win, fneed)
    case B.Pieces{ps}:
      inject.r(o, run, b, lf, ps, B.Line.term(l), cx, win)
    case B.Unsplit{+c}:
      +fs = J.pfs(B.Line.body(l))
      slow.vd(o, run, l, fs, s, lf, b, cx, fneed, back, vd.unsplit(c, R.Opts.strict(o), fs, B.Line.body(l), verdict(back, win, fs, B.Line.body(l))))

def slow.parts(r: Cx & B.Parts, +back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, win: Win, +fneed: Bool) -> Adv:
  (cx, pt) = r
  slow.parts.k(pt, cx, back, o, run, l, s, lf, b, win, fneed)

def slow.split(split: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match split:
    case False{}:
      slow.whole(back, o, run, l, s, lf, b, cx, win, fneed)
    case True{}:
      slow.parts(Cx.parts(cx, o, B.Line.body(l)), back, o, run, l, s, lf, b, win, fneed)

# A body line the fast path did not take: judged on its text; with -m, split
# first (B.Rec.parts: the records are read next, or the line is refused).
def slow(+back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  slow.split(R.Opts.split(o), back, o, run, l, s, lf, b, cx, win, fneed)

# The held header has at most 2^28 bytes.
def Run.head(r: NR.Run) -> NR.Run & Bool:
  match r:
    case NR.Run{n, i, +h, c, cb, e, l, f, bk, bn, tl, k, ob, ow, ns, x}:
      (NR.Run{n, i, h, c, cb, e, l, f, bk, bn, tl, k, ob, ow, ns, x}, len_le(h, 268435456))

def head.fits(fits: Bool, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, +back: Nat, cx: Cx, win: Win) -> Adv:
  match fits:
    case True{}:
      done.b(o, (NR.head_line(True{}, NR.tick(run), o, l), b), (lf + 1 : U32), Cx.line(cx, B.Line.body(l)), win)
    case False{}:
      to_str(o, run, b, s, back, cx, win, False{})

def head.len(+o: B.Opts, p: NR.Run & Bool, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, +back: Nat, cx: Cx, win: Win) -> Adv:
  (run, hok) = p
  head.fits(hok && len_le(R.added(o, B.Line.term(l)), 268435456) && len_le(B.Line.text(l), 268435456), o, run, l, s, lf, b, back, cx, win)

# A header line: held; the #CHROM line writes the header, which must fit:
# the held header, the added lines and the line's text (with its LF) at most
# 2^28 bytes each.
def head(isc: Bool, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, +back: Nat, cx: Cx, win: Win) -> Adv:
  match isc:
    case False{}:
      done.b(o, (NR.head_line(False{}, NR.tick(run), o, l), b), (lf + 1 : U32), Cx.line(cx, B.Line.body(l)), win)
    case True{}:
      head.len(o, Run.head(run), l, s, lf, b, back, cx, win)

def decoded.go(inbody: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +l: B.Line, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match inbody:
    case False{}:
      head(R.is_chrom_line(B.Line.body(l)), o, run, l, s, lf, b, back, cx, win)
    case True{}:
      slow(back, o, run, l, s, lf, b, cx, win, fneed)

def decoded.k(inbody: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +lf: U32, p: D.Bytes & String, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (b, +t) = p
  +l = line(t)
  decoded.go(inbody, back, o, run, l, s, lf, b, cx, win, fneed)

def Run.inbody(r: NR.Run) -> NR.Run & Bool:
  match r:
    case NR.Run{n, +i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, i)

def decoded.in(+back: Nat, +o: B.Opts, p: NR.Run & Bool, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (run, inb) = p
  decoded.k(inb, back, o, run, s, lf, text(b, s, (lf - s : U32)), cx, win, fneed)

def pend.add.b(p: D.Bytes & D.Bytes) -> Pd:
  (q, b) = p
  PB{q}

def pend.add.bk(small: Bool, p: D.Bytes, b: D.Bytes, +s: U32, +n: U32) -> Pd:
  match small:
    case True{}:
      pend.add.b(NR.put_bytes(p, b, s, n))
    case False{}:
      PS{text_of(p) ++ text.all(text(b, s, n))}

def pend.add.b0(r: D.Bytes & U32, b: D.Bytes, +s: U32, +n: U32) -> Pd:
  (p, +m) = r
  pend.add.bk(U32.is_le((m + n : U32), 268435456), p, b, s, n)

# Bytes s .. s+n-1 of b added at the end of pend: as bytes while pend stays
# within 2^28 bytes (pend holds at most 2^28, a piece at most 2^31: the sum
# does not wrap), else as text.
def pend.add(pd: Pd, b: D.Bytes, +s: U32, +n: U32) -> Pd:
  match pd:
    case PB{p}:
      pend.add.b0(BY.len(p), b, s, n)
    case PS{x}:
      PS{x ++ text.all(text(b, s, n))}

def Pd.len(pd: Pd) -> Pd & Nat:
  match pd:
    case PB{b}:
      D.Bytes{+n, buf} = b
      (PB{D.Bytes{n, buf}}, U32.to_nat(n))
    case PS{+s}:
      (PS{s}, String.length(s))

# The rest of a buffer that holds no complete line goes to pend.
def part.len(+o: B.Opts, md: Md, +back: Nat, +s: U32, r: D.Bytes & U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (b, +len) = r
  match cx:
    case Cx{rest, pend, eof, dfs, hold}:
      Went{St{o, md, rest, pend.add(pend, b, s, (len - s : U32)), eof, back, win, None{}, fneed, dfs}}

def decoded.big(big: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match big:
    case True{}:
      to_str(o, run, b, s, back, cx, win, fneed)
    case False{}:
      decoded.in(back, o, Run.inbody(run), s, lf, b, cx, win, fneed)

def decoded.if(part: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match part:
    case True{}:
      part.len(o, MB{run}, back, s, BY.len(b), cx, win, fneed)
    case False{}:
      decoded.big(U32.is_lt(268435456, (lf - s : U32)), back, o, run, s, lf, b, cx, win, fneed)

def decoded.lf(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, t: NF.Tb, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match t:
    case NF.Tb{b, +j, +part, x}:
      decoded.if(part, back, o, run, s, j, b, cx, win, fneed)

# The line at s, decoded and handled on its text (a line of more than 2^28
# bytes switches the run to the String mode first).
def decoded(+back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  decoded.lf(back, o, run, s, NF.lf(b, s), cx, win, fneed)

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

# The record against the last answer (a window read in parts is the slow
# path's).
def against(w: Win, b: D.Bytes, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32) -> Wo:
  match w:
    case WKnown{+c, cb, +a0, +b0, +clen, +off, raw, +offu, +rlen, +clenu}:
      win.same(c, a0, b0, clen, off, raw, offu, rlen, clenu, pos, rs, rl, NF.same(b, s, (e0 - s : U32), cb))
    case WUnk{c}:
      Wo{WUnk{c}, b, WMiss{}}
    case WNone{}:
      Wo{WNone{}, b, WNeed{}}
    case WStr{c, a0, b0, clen, off, raw}:
      Wo{WStr{c, a0, b0, clen, off, raw}, b, WMiss{}}

# ---------------------------------------------------------------------------
# A record rewritten on its bytes (norm_fix.bend)
# ---------------------------------------------------------------------------

def fix.out(+o: B.Opts, p: NR.Run & D.Bytes, +lf: U32, b: D.Bytes, cx: Cx, win: Win) -> Adv:
  (run, sc) = p
  done.b(o, (run, b), (lf + 1 : U32), cx, win)

def fix.tick(+o: B.Opts, p: NR.Run & Nat, +q: Nat, +pos: U32, +lf: U32, b: D.Bytes, sc: D.Bytes, +m: U32, cx: Cx, win: Win) -> Adv:
  (run, +n) = p
  fix.out(o, NR.fix_done(run, R.Opts.w(o), n, q, U32.to_nat(pos), sc, m), lf, b, cx, win)

# The new text must fit the output buffer, as the String path's res_fits
# asks; else the run goes to the String mode (body.fits).
def fix.fits(fits: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +q: Nat, +pos: U32, +s: U32, +lf: U32, b: D.Bytes, sc: D.Bytes, +m: U32, cx: Cx, win: Win) -> Adv:
  match fits:
    case True{}:
      fix.tick(o, ticked(run), q, pos, lf, b, sc, m, cx, win)
    case False{}:
      to_str(o, run, b, s, back, cx, win, False{})

def fix.len(+back: Nat, +o: B.Opts, p: NR.Run & U32, +q: Nat, +pos: U32, +s: U32, +lf: U32, b: D.Bytes, r: D.Bytes & U32, cx: Cx, win: Win) -> Adv:
  (run, +ol) = p
  (sc, +m) = r
  fix.fits(U32.is_le(m, (1073741824 - ol : U32)), back, o, run, q, pos, s, lf, b, sc, m, cx, win)

def fix.ne(eq: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +q: Nat, +pos: U32, +s: U32, +lf: U32, sc: D.Bytes, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match eq:
    case False{}:
      fix.len(back, o, Run.oblen(run), q, pos, s, lf, b, BY.len(sc), cx, win)
    case True{}:
      decoded(back, o, run, b, s, cx, win, fneed)

def fix.cmp.k(+back: Nat, +o: B.Opts, run: NR.Run, +q: Nat, +pos: U32, +s: U32, +lf: U32, r: D.Bytes & (D.Bytes & Bool), cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (sc, p) = r
  (b, eq) = p
  fix.ne(eq, back, o, run, q, pos, s, lf, sc, b, cx, win, fneed)

def fix.cmp.if(same_len: Bool, sc: D.Bytes, b: D.Bytes, +s: U32, +m: U32) -> D.Bytes & (D.Bytes & Bool):
  match same_len:
    case True{}:
      BY.same(sc, 0, b, s, m)
    case False{}:
      (sc, (b, False{}))

def fix.cmp(+back: Nat, +o: B.Opts, run: NR.Run, +q: Nat, +pos: U32, +s: U32, +lf: U32, r: D.Bytes & U32, b: D.Bytes, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (sc, +m) = r
  fix.cmp.k(back, o, run, q, pos, s, lf, fix.cmp.if(U32.is_eq(m, ((lf + 1 : U32) - s : U32)), sc, b, s, m), cx, win, fneed)

# The new line is written (else, or if it is the line as it came, the line
# is judged on its text).
def fix.wb(+back: Nat, +o: B.Opts, run: NR.Run, +q: Nat, +pos: U32, +s: U32, +lf: U32, cx: Cx, +c0: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, +fneed: Bool, wb: NX.Wb) -> Adv:
  match wb:
    case NX.Wb{sc, b, raw, True{}}:
      fix.cmp(back, o, run, q, pos, s, lf, BY.len(sc), b, cx, WKnown{c0, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, fneed)
    case NX.Wb{sc, b, raw, False{}}:
      decoded(back, o, run, b, s, cx, WKnown{c0, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, fneed)

# same: the variant is unchanged and written in upper case (J.fast's Same):
# left to the String path.
def fix.same(same: Bool, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +c: NF.Cut, +lf: U32, +als: List<&2, NX.Ap>, +k: U32, +tr: U32, +d: Nat, cx: Cx, +c0: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, +fneed: Bool, b: D.Bytes, raw: D.Bytes) -> Adv:
  match same:
    case True{}:
      decoded(back, o, run, b, s, cx, WKnown{c0, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, fneed)
    case False{}:
      fix.wb(back, o, run, U32.to_nat(((pos - k : U32) + U32.from_nat(d) : U32)), pos, s, lf, cx, c0, cb, a0, b0, clen, off, offu, rlen, clenu, fneed, NX.write(b, raw, s, c, als, k, tr, d, pos, offu))

def fix.nr(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +c: NF.Cut, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, cx: Cx, +c0: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, +fneed: Bool, r: NX.Nr) -> Adv:
  match r:
    case NX.Ng{b, raw}:
      decoded(back, o, run, b, s, cx, WKnown{c0, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, fneed)
    case NX.Nd{b, raw, +k, +tr, +d}:
      fix.same(U32.is_zero(k) && U32.is_zero(tr) && Nat.is_eq(d, 0n) && up, back, o, run, s, pos, c, lf, als, k, tr, d, cx, c0, cb, a0, b0, clen, off, offu, rlen, clenu, fneed, b, raw)

def fix.hit(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +c: NF.Cut, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, cx: Cx, win: Win, b: D.Bytes, +fneed: Bool) -> Adv:
  match win:
    case WKnown{+c0, cb, +a0, +b0, +clen, +off, raw, +offu, +rlen, +clenu}:
      fix.nr(back, o, run, s, pos, c, lf, als, up, cx, c0, cb, a0, b0, clen, off, offu, rlen, clenu, fneed, NX.norm(b, raw, als, pos, offu))
    case w:
      decoded(back, o, run, b, s, cx, w, fneed)

def fix.wo(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +c: NF.Cut, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, wo: Wo, cx: Cx, +fneed: Bool) -> Adv:
  match wo:
    case Wo{win, b, WHit{}}:
      fix.hit(back, o, run, s, pos, c, lf, als, up, cx, win, b, fneed)
    case Wo{win, b, r}:
      decoded(back, o, run, b, s, cx, win, fneed)

def fix.if(ok: Bool, +back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, +pos: U32, +c: NF.Cut, +e0: U32, +e2: U32, +e3: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match ok:
    case True{}:
      fix.wo(back, o, run, s, pos, c, lf, als, up, against(win, b, s, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), cx, fneed)
    case False{}:
      decoded(back, o, run, b, s, cx, win, fneed)

def fix.run.q(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +c: NF.Cut, +e0: U32, +e2: U32, +e3: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, q: D.Bytes & Bool, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (b, ok) = q
  fix.if(ok && U32.is_lt(s, e0) && U32.is_le((lf - s : U32), 268435456), back, o, run, b, s, pos, c, e0, e2, e3, lf, als, up, cx, win, fneed)

def fix.run(+back: Nat, +o: B.Opts, p: NR.Run & (D.Bytes & Bool), +s: U32, +pos: U32, +c: NF.Cut, +e0: U32, +e2: U32, +e3: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (run, q) = p
  fix.run.q(back, o, run, s, pos, c, e0, e2, e3, lf, als, up, q, cx, win, fneed)

def fix.pre(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, r: NX.Fr, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match r:
    case NX.Fr{b, NX.Fix{+pos, NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}, +als, +up}}:
      fix.run(back, o, Run.same(run, b, s, e0), s, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, cx, win, fneed)
    case NX.Fr{b, p}:
      decoded(back, o, run, b, s, cx, win, fneed)

# A body line the fast path did not take: rewritten on its bytes when it
# passes norm_fix.bend's tests, the CHROM run's and the window's (as the fast
# path's WHit), and the window reaches far enough left; else judged on its
# text.
def fix(+back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  fix.pre(back, o, run, s, NX.line(b, s), cx, win, fneed)

def fast.hit(+o: B.Opts, p: NR.Run & Nat, +pos: U32, +s: U32, +lf: U32, b: D.Bytes, cx: Cx, win: Win) -> Adv:
  (run, +n) = p
  done.b(o, NR.fast_done(run, R.Opts.w(o), n, U32.to_nat(pos), b, s, (lf + 1 - s : U32)), (lf + 1 : U32), cx, win)

# The window does not hold the record: ask for one that does (once per line;
# after that, the line takes the slow path).
def fast.need(+o: B.Opts, p: NR.Run & String, +back: Nat, +pos: U32, +rl: U32, b: D.Bytes, +s: U32, cx: Cx, win: Win) -> Adv:
  (run, +c) = p
  +p1 = Nat.sub(U32.to_nat(pos), 1n)
  want.b(o, run, b, s, back, cx, win, Req.of(c, p1, Nat.add(p1, U32.to_nat(rl))), True{})

def fast.wo(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +lf: U32, +rl: U32, wo: Wo, cx: Cx, fneed: Bool) -> Adv:
  match wo fneed:
    case Wo{win, b, WHit{}} _:
      fast.hit(o, ticked(run), pos, s, lf, b, cx, win)
    case Wo{win, b, WNeed{}} False{}:
      fast.need(o, Run.cur(run), back, pos, rl, b, s, cx, win)
    case Wo{win, b, WNeed{}} True{}:
      decoded(back, o, run, b, s, cx, win, True{})
    case Wo{win, b, WMiss{}} +f:
      decoded(back, o, run, b, s, cx, win, f)

def fast.run.if(ok: Bool, +back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, +pos: U32, +lf: U32, +e0: U32, +rs: U32, +rl: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match ok:
    case True{}:
      fast.wo(back, o, run, s, pos, lf, rl, against(win, b, s, e0, pos, rs, rl), cx, fneed)
    case False{}:
      decoded(back, o, run, b, s, cx, win, fneed)

def fast.run.q(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +pos: U32, +lf: U32, +e0: U32, +rs: U32, +rl: U32, q: D.Bytes & Bool, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (b, ok) = q
  fast.run.if(ok && U32.is_lt(s, e0) && U32.is_le((lf - s : U32), 268435456), back, o, run, b, s, pos, lf, e0, rs, rl, cx, win, fneed)

def fast.run(+back: Nat, +o: B.Opts, p: NR.Run & (D.Bytes & Bool), +s: U32, +pos: U32, +lf: U32, +e0: U32, +rs: U32, +rl: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (run, q) = p
  fast.run.q(back, o, run, s, pos, lf, e0, rs, rl, q, cx, win, fneed)

def fast.pre(+back: Nat, +o: B.Opts, run: NR.Run, +s: U32, pr: NF.Pr, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match pr:
    case NF.Pr{b, NF.Pass{+pos, +e0, e1, +e2, +e3, e4, e5, e6, e7, +lf}}:
      fast.run(back, o, Run.same(run, b, s, e0), s, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), cx, win, fneed)
    case NF.Pr{b, NF.Slow{}}:
      fix(back, o, run, b, s, cx, win, fneed)
    case NF.Pr{b, NF.Incomplete{}}:
      decoded(back, o, run, b, s, cx, win, fneed)

def split.out(o2: NS.Out, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, +lf: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match o2:
    case NS.Out{b, Some{recs}}:
      inject(o, run, b, lf, recs, cx, win)
    case NS.Out{b, None{}}:
      decoded(back, o, run, b, s, cx, win, fneed)

def split.b(+back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, +lf: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match cx:
    case Cx{rest, pend, eof, +dfs, hold}:
      split.out(NS.split(b, s, lf, R.Opts.over0(o), dfs), back, o, run, s, lf, Cx{rest, pend, eof, dfs, hold}, win, fneed)

def body.multi(r: D.Bytes & Maybe<&2, U32>, +back: Nat, +o: B.Opts, run: NR.Run, +s: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (b, m) = r
  match m:
    case Some{+lf}:
      split.b(back, o, run, b, s, lf, cx, win, fneed)
    case None{}:
      fast.pre(back, o, run, s, NF.line(b, s), cx, win, fneed)

# A body line in the byte mode: with -m, a line whose ALT has a comma is
# split on its bytes (norm_split.bend), or else on its text (slow).
def body.m(split: Bool, +back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match split:
    case False{}:
      fast.pre(back, o, run, s, NF.line(b, s), cx, win, fneed)
    case True{}:
      body.multi(NS.multi(b, s), back, o, run, s, cx, win, fneed)

def body.if(inbody: Bool, +back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  match inbody:
    case True{}:
      body.m(R.Opts.split(o), back, o, run, b, s, cx, win, fneed)
    case False{}:
      decoded(back, o, run, b, s, cx, win, fneed)

def body.k(+back: Nat, +o: B.Opts, p: NR.Run & Bool, b: D.Bytes, +s: U32, cx: Cx, win: Win, +fneed: Bool) -> Adv:
  (run, inb) = p
  body.if(inb, back, o, run, b, s, cx, win, fneed)

def Run.rs(r: NR.Run) -> NR.Run & Rs:
  match r:
    case NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, +ow, ns, +x}:
      D.Bytes{+len, buf} = ob
      (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, D.Bytes{len, buf}, ow, ns, x}, Rs{x, U32.is_le(1073741824, ow), U32.is_le(536870912, len)})

def rs_untick(st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{Nat.sub(n, 1n), i, h, c, e, l, b, k, o, ns, x}

def sp.b.if(done: Bool, +back: Nat, +o: B.Opts, run: NR.Run, b: D.Bytes, +s: U32, rest: List<&1, Src>, pend: Pd, eof: Bool, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  match done:
    case True{}:
      Went{St{o, MB{run}, rest, pend, eof, back, win, None{}, fneed, dfs}}
    case False{}:
      body.k(back, o, Run.inbody(NR.untick(run)), b, s, Cx{rest, pend, eof, dfs, True{}}, win, fneed)

# The next record of a split line, in the byte mode: handled as a line with
# the split line's number (the run unticked first); a buffer whose records
# are all handled is dropped.
def sp.b(+back: Nat, +o: B.Opts, run: NR.Run, r: D.Bytes & U32, +s: U32, rest: List<&1, Src>, pend: Pd, eof: Bool, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  (b, +len) = r
  sp.b.if(U32.is_le(len, s), back, o, run, b, s, rest, pend, eof, win, asked, fneed, dfs)

# The next line of the input in the byte mode.
def mb.src(src: List<&1, Src>, +o: B.Opts, run: NR.Run, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  match src:
    case Nil{}:
      Idle{St{o, MB{run}, Nil{}, pend, eof, back, win, asked, fneed, dfs}}
    case SB{b, +s} <> rest:
      body.k(back, o, Run.inbody(run), b, s, Cx{rest, pend, eof, dfs, False{}}, win, fneed)
    case SP{b, +s} <> rest:
      sp.b(back, o, run, BY.len(b), s, rest, pend, eof, win, asked, fneed, dfs)
    case SL{p} <> rest:
      Went{St{o, to_ms(run), SL{p} <> rest, pend, eof, back, win, None{}, fneed, dfs}}
    case SR{l} <> rest:
      Went{St{o, to_ms(run), SR{l} <> rest, pend, eof, back, win, None{}, fneed, dfs}}

def mb.rs(p: NR.Run & Rs, +o: B.Opts, src: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  (run, rs) = p
  match rs:
    case Rs{True{}, f, g}:
      Ended{St{o, MB{run}, src, pend, eof, back, win, asked, fneed, dfs}}
    case Rs{False{}, True{}, g}:
      Yield{St{o, MB{run}, src, pend, eof, back, win, asked, fneed, dfs}}
    case Rs{False{}, False{}, True{}}:
      Went{St{o, to_ms(run), src, pend, eof, back, win, None{}, fneed, dfs}}
    case Rs{False{}, False{}, False{}}:
      mb.src(src, o, run, pend, eof, back, win, asked, fneed, dfs)

def ms.part.len(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +at: U32, r: D.Bytes & U32, rest: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, +fneed: Bool, dfs: B.Defs, hold: Bool) -> Adv:
  (b, +len) = r
  Went{St{o, MS{s, qs, ql, None{}}, rest, pend.add(pend, b, at, (len - at : U32)), eof, back, win, None{}, fneed, dfs}}

# A line read from a buffer: a text line, or (hold) a record of a split line,
# which a Want then puts back as a record (SR), counted again.
def ls.of(+hold: Bool, +t: String) -> Ls:
  match hold:
    case True{}:
      LsR{line(t)}
    case False{}:
      LsT{t}

def ms.sb.k(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +at: U32, +lf: U32, p: D.Bytes & String, rest: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, dfs: B.Defs, +hold: Bool) -> Adv:
  (b, +t) = p
  ms.line(o, s, qs, ql, ls.of(hold, t), back, Cx{Src.of(hold, b, (lf + 1 : U32)) <> rest, pend, eof, dfs, hold}, win)

def ms.sb.if(part: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, b: D.Bytes, +at: U32, +lf: U32, rest: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, +fneed: Bool, dfs: B.Defs, hold: Bool) -> Adv:
  match part:
    case True{}:
      ms.part.len(o, s, qs, ql, at, BY.len(b), rest, pend, eof, back, win, fneed, dfs, hold)
    case False{}:
      ms.sb.k(o, s, qs, ql, at, lf, text(b, at, (lf - at : U32)), rest, pend, eof, back, win, dfs, hold)

def ms.sb(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +at: U32, t: NF.Tb, rest: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, +fneed: Bool, dfs: B.Defs, hold: Bool) -> Adv:
  match t:
    case NF.Tb{b, +j, +part, x}:
      ms.sb.if(part, o, s, qs, ql, b, at, j, rest, pend, eof, back, win, fneed, dfs, hold)

def sp.s.if(done: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, b: D.Bytes, +at: U32, rest: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  match done:
    case True{}:
      Went{St{o, MS{s, qs, ql, None{}}, rest, pend, eof, back, win, None{}, fneed, dfs}}
    case False{}:
      ms.sb(o, rs_untick(s), qs, ql, at, NF.lf(b, at), rest, pend, eof, back, win, fneed, dfs, True{})

# The same in the String mode.
def sp.s(+o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, r: D.Bytes & U32, +at: U32, rest: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  (b, +len) = r
  sp.s.if(U32.is_le(len, at), o, s, qs, ql, b, at, rest, pend, eof, back, win, asked, fneed, dfs)

# The next line of the input in the String mode.
def ms.src(src: List<&1, Src>, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  match src:
    case Nil{}:
      Idle{St{o, MS{s, qs, ql, None{}}, Nil{}, pend, eof, back, win, asked, fneed, dfs}}
    case SB{b, +at} <> rest:
      ms.sb(o, s, qs, ql, at, NF.lf(b, at), rest, pend, eof, back, win, fneed, dfs, False{})
    case SL{+p} <> rest:
      ms.line(o, s, qs, ql, LsT{p}, back, Cx{rest, pend, eof, dfs, False{}}, win)
    case SR{+l} <> rest:
      ms.line(o, rs_untick(s), qs, ql, LsR{l}, back, Cx{rest, pend, eof, dfs, True{}}, win)
    case SP{b, +at} <> rest:
      sp.s(o, s, qs, ql, BY.len(b), at, rest, pend, eof, back, win, asked, fneed, dfs)

def ms.full(full: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, src: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  match full:
    case True{}:
      Yield{St{o, MS{s, qs, ql, None{}}, src, pend, eof, back, win, asked, fneed, dfs}}
    case False{}:
      ms.src(src, o, s, qs, ql, pend, eof, back, win, asked, fneed, dfs)

def ms.adv(halt: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, code: Maybe<&2, Nat>, src: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Adv:
  match halt code:
    case _ Some{c}:
      Ended{St{o, MS{s, qs, ql, Some{c}}, src, pend, eof, back, win, asked, fneed, dfs}}
    case True{} None{}:
      Ended{St{o, MS{s, qs, ql, None{}}, src, pend, eof, back, win, asked, fneed, dfs}}
    case False{} None{}:
      ms.full(Nat.is_le(lim(), ql), o, s, qs, ql, src, pend, eof, back, win, asked, fneed, dfs)

# Handle the next complete line, if any.
def advance(st: St) -> Adv:
  match st:
    case St{+o, MB{run}, src, pend, eof, +back, win, asked, +fneed, dfs}:
      mb.rs(Run.rs(run), o, src, pend, eof, back, win, asked, fneed, dfs)
    case St{+o, MS{+s, qs, +ql, code}, src, pend, eof, +back, win, asked, +fneed, dfs}:
      ms.adv(R.RunSt.halt(s), o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed, dfs)

def ms.take.c(c: Cut2, s: R.RunSt, ns: List<&2, B.Note>, code: Maybe<&2, Nat>) -> (D.Bytes & List<&2, B.Note>) & Md:
  match c:
    case Cut2{now, +later}:
      ((NR.of_str(now), ns), MS{s, [later], String.length(later), code})

# What a String-mode step hands out: at most lim() bytes of its output, and
# its messages; the rest stays.
def ms.take.k(+t: String, s: R.RunSt, code: Maybe<&2, Nat>) -> (D.Bytes & List<&2, B.Note>) & Md:
  match s:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ms.take.c(take_w(t, 1073741824), R.RunSt{n, i, h, c, e, l, b, k, o, Nil{}, x}, ns, code)

def cat.go(xs: List<&2, String>, h: String) -> String:
  match xs:
    case Nil{}:
      h
    case x <> t:
      h ++ cat.go(t, x)

# String.concat, without copying the last piece.
def cat(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      cat.go(t, x)

def ms.take(s: R.RunSt, qs: List<&2, String>, code: Maybe<&2, Nat>) -> (D.Bytes & List<&2, B.Note>) & Md:
  ms.take.k(cat(List.reverse(&2, String, qs)), s, code)

def md.take.k(p: (D.Bytes & List<&2, B.Note>) & NR.Run) -> (D.Bytes & List<&2, B.Note>) & Md:
  (on, run) = p
  (on, MB{run})

# What the step wrote (bytes, messages in order); left: the input bytes not
# handled yet (the byte mode sizes its next buffer by it).
def md.take(md: Md, +left: U32) -> (D.Bytes & List<&2, B.Note>) & Md:
  match md:
    case MB{run}:
      md.take.k(NR.take(run, left))
    case MS{s, qs, ql, code}:
      ms.take(s, qs, code)

def out.fin(on: D.Bytes & List<&2, B.Note>, st: St, nx: P.Next) -> Step:
  (b, ns) = on
  Step{st, b, ns, nx}

def out.k(p: (D.Bytes & List<&2, B.Note>) & Md, +o: B.Opts, src: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs, nx: P.Next) -> Step:
  (on, md) = p
  out.fin(on, St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, nx)

def out.left(+o: B.Opts, md: Md, p: List<&1, Src> & U32, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs, nx: P.Next) -> Step:
  (src, +n) = p
  out.k(md.take(md, n), o, src, pend, eof, back, win, asked, fneed, dfs, nx)

def left.one(+at: U32, r: D.Bytes & U32) -> Src & U32:
  (b, +len) = r
  (SB{b, at}, (len - at : U32))

def left.sp(+at: U32, r: D.Bytes & U32) -> Src & U32:
  (b, +len) = r
  (SP{b, at}, (len - at : U32))

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
    case SB{b, +at} <> t:
      left.cons(left.one(at, BY.len(b)), left(t))
    case SL{p} <> t:
      left.cons((SL{p}, 0), left(t))
    case SP{b, +at} <> t:
      left.cons(left.sp(at, BY.len(b)), left(t))
    case SR{l} <> t:
      left.cons((SR{l}, 0), left(t))

# The step ends: what it wrote, and what next.
def out(st: St, nx: P.Next) -> Step:
  match st:
    case St{+o, md, src, pend, eof, +back, win, asked, +fneed, dfs}:
      out.left(o, md, left(src), pend, eof, back, win, asked, fneed, dfs, nx)

def fin.mb(+o: B.Opts, p: NR.Run & Nat, src: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Step:
  (run, +code) = p
  out(St{o, MB{run}, src, pend, eof, back, win, asked, fneed, dfs}, P.Finish{code})

def fin.ms.go(fits: Bool, +o: B.Opts, s: R.RunSt, qs: List<&2, String>, +ql: Nat, +code: Nat, src: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Step:
  match fits:
    case True{}:
      out(St{o, MS{s, qs, ql, Some{code}}, src, pend, eof, back, win, asked, fneed, dfs}, P.Finish{code})
    case False{}:
      out(St{o, MS{s, qs, ql, Some{code}}, src, pend, eof, back, win, asked, fneed, dfs}, P.Ask{Nil{}})

# The String mode's report: its output and messages are handed out over as
# many steps as the output needs, then it stops.
def fin.ms(rep: R.Report, +o: B.Opts, s: R.RunSt, +qs: List<&2, String>, +ql: Nat, src: List<&1, Src>, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Step:
  match rep s:
    case R.Report{+out, ns, +code} R.RunSt{n, i, h, c, e, l, b, k, o2, ns0, x}:
      fin.ms.go(len_le(cat(List.reverse(&2, String, out <> qs)), 1073741824), o, R.RunSt{n, i, h, c, e, l, b, k, "", ns, x}, out <> qs, Nat.add(ql, String.length(out)), code, src, pend, eof, back, win, asked, fneed, dfs)

# The end of the run: the buffer is written (run.bend's finish) and the
# program stops.
def finish(st: St) -> Step:
  match st:
    case St{+o, MB{run}, src, pend, eof, +back, win, asked, +fneed, dfs}:
      fin.mb(o, NR.finish(run, R.Opts.w(o)), src, pend, eof, back, win, asked, fneed, dfs)
    case St{+o, MS{+s, +qs, +ql, None{}}, src, pend, eof, +back, win, asked, +fneed, dfs}:
      fin.ms(R.finish(s), o, s, qs, ql, src, pend, eof, back, win, asked, fneed, dfs)
    case St{+o, MS{s, +qs, +ql, Some{+code}}, src, pend, eof, +back, win, asked, +fneed, dfs}:
      fin.ms.go(len_le(cat(List.reverse(&2, String, qs)), 1073741824), o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed, dfs)

def idle(st: St) -> Step:
  match st:
    case St{o, md, src, pend, True{}, back, win, asked, fneed, dfs}:
      finish(St{o, md, src, pend, True{}, back, win, asked, fneed, dfs})
    case St{o, md, src, pend, False{}, back, win, asked, fneed, dfs}:
      out(St{o, md, src, pend, False{}, back, win, asked, fneed, dfs}, P.More{})

def fuel.cons2(s: Src, +n: U32, q: List<&1, Src> & Nat) -> List<&1, Src> & Nat:
  (t, +m) = q
  (s <> t, Nat.add(Nat.add(U32.to_nat(n), 2n), m))

def fuel.cons(p: Src & U32, q: List<&1, Src> & Nat) -> List<&1, Src> & Nat:
  (s, +n) = p
  fuel.cons2(s, n, q)

def fuel.src(src: List<&1, Src>) -> List<&1, Src> & Nat:
  match src:
    case Nil{}:
      (Nil{}, 0n)
    case SB{b, +at} <> t:
      fuel.cons(left.one(at, BY.len(b)), fuel.src(t))
    case SL{p} <> t:
      fuel.cons((SL{p}, 0), fuel.src(t))
    case SP{b, +at} <> t:
      fuel.cons(left.sp(at, BY.len(b)), fuel.src(t))
    case SR{l} <> t:
      fuel.cons((SR{l}, 0), fuel.src(t))

# Handle lines while the records' fuel lasts (with -m, the records a split
# line makes during the pump). Ends at the first Adv that is not Went, or at
# a Went once this fuel is spent (pump then refills it).
def pump.r(fuel: Nat, a: Adv) -> Adv:
  match fuel a:
    case 1n+f Went{st}:
      pump.r(f, advance(st))
    case _ a2:
      a2

# The state and its sources' fuel (fuel.src).
def fuel.st.k(+o: B.Opts, md: Md, p: List<&1, Src> & Nat, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St & Nat:
  (src, +n) = p
  (St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, n)

def fuel.st(st: St) -> St & Nat:
  match st:
    case St{+o, md, src, pend, eof, +back, win, asked, +fneed, dfs}:
      fuel.st.k(o, md, fuel.src(src), pend, eof, back, win, asked, fneed, dfs)

# pump.r with its fuel refilled from the state.
def pump.fill(p: St & Nat) -> Adv:
  (st, +n) = p
  pump.r(n, advance(st))

# Handle lines until one needs the reference, none is left, the run stops, or
# the fuel runs out (the step then ends and the next one goes on: P.Ask{[]}
# gets another step whether or not the file ended). Two fuels: this one for
# the input's lines, and pump.r's, refilled from the state each time it is
# spent, for the records of split lines (-m) made meanwhile. With the measure
# ordered by the input, then the records, neither runs out.
def pump(fuel: Nat, a: Adv) -> Step:
  match fuel a:
    case 0n Went{st}:
      out(st, P.Ask{Nil{}})
    case 1n+f Went{st}:
      pump(f, pump.fill(fuel.st(st)))
    case _ Want{st, r}:
      out(st, P.Ask{r})
    case _ Idle{st}:
      idle(st)
    case _ Ended{st}:
      finish(st)
    case _ Yield{st}:
      out(st, P.Ask{Nil{}})

def go.k(+o: B.Opts, md: Md, p: List<&1, Src> & Nat, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> Step:
  (src, +n) = p
  pump(1n+Nat.add(n, 1n), advance(St{o, md, src, pend, eof, back, win, asked, fneed, dfs}))

# Pump with fuel for every line in the input (each takes at least one byte;
# each buffer two more, and one more for a change of form).
def go(st: St) -> Step:
  match st:
    case St{+o, md, src, pend, eof, +back, win, asked, +fneed, dfs}:
      go.k(o, md, fuel.src(src), pend, eof, back, win, asked, fneed, dfs)

# A complete line as input: bytes (with their LF), or text (without it).
def Pd.src(pd: Pd) -> Src:
  match pd:
    case PB{b}:
      SB{b, 0}
    case PS{s}:
      SL{s}

# ---------------------------------------------------------------------------
# Input
# ---------------------------------------------------------------------------

def feed.join(+o: B.Opts, md: Md, +k: U32, p: Pd & D.Bytes, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  (j, b) = p
  St{o, md, [Pd.src(j), SB{b, (k + 1 : U32)}], PB{BY.empty(0n)}, eof, back, win, asked, fneed, dfs}

def join.b(p: D.Bytes & D.Bytes) -> Pd & D.Bytes:
  (q, b) = p
  (PB{q}, b)

def join.s(+s: String, p: D.Bytes & String) -> Pd & D.Bytes:
  (b, +t) = p
  (PS{s ++ t}, b)

def join.go(small: Bool, p: D.Bytes, b: D.Bytes, +k: U32) -> Pd & D.Bytes:
  match small:
    case True{}:
      join.b(NR.put_bytes(p, b, 0, (k + 1 : U32)))
    case False{}:
      join.s(text_of(p), text(b, 0, k))

def join.l(+k: U32, r: D.Bytes & U32, b: D.Bytes) -> Pd & D.Bytes:
  (p, +m) = r
  join.go(U32.is_le(((m + k : U32) + 1 : U32), 268435456), p, b, k)

# The line end completed by bytes 0 .. k of b (k: the first LF): bytes while
# it stays within 2^28 bytes, else text (without the LF).
def join.k(pd: Pd, b: D.Bytes, +k: U32) -> Pd & D.Bytes:
  match pd:
    case PB{p}:
      join.l(k, BY.len(p), b)
    case PS{s}:
      join.s(s, text(b, 0, k))

def feed.all(+o: B.Opts, md: Md, r: D.Bytes & U32, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  (b, +n) = r
  St{o, md, Nil{}, pend.add(pend, b, 0, n), eof, back, win, asked, fneed, dfs}

def feed.lf(none: Bool, +o: B.Opts, md: Md, b: D.Bytes, +k: U32, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  match none:
    case True{}:
      feed.all(o, md, BY.len(b), pend, eof, back, win, asked, fneed, dfs)
    case False{}:
      feed.join(o, md, k, join.k(pend, b, k), eof, back, win, asked, fneed, dfs)

def feed.find(+o: B.Opts, md: Md, t: NF.Tb, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  match t:
    case NF.Tb{b, +k, +none, x}:
      feed.lf(none, o, md, b, k, pend, eof, back, win, asked, fneed, dfs)

def feed.if(empty: Bool, +o: B.Opts, md: Md, src: List<&1, Src>, b: D.Bytes, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  match empty:
    case True{}:
      St{o, md, List.append(&1, Src, src, [SB{b, 0}]), pend, eof, back, win, asked, fneed, dfs}
    case False{}:
      feed.find(o, md, NF.lf(b, 0), pend, eof, back, win, asked, fneed, dfs)

def feed.k(+o: B.Opts, md: Md, src: List<&1, Src>, b: D.Bytes, r: Pd & Nat, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  (pend, +n) = r
  feed.if(Nat.is_eq(n, 0n), o, md, src, b, pend, eof, back, win, asked, fneed, dfs)

# The byte run's output buffer gets room for a piece's bytes.
def md.reserve(md: Md, +n: U32) -> Md:
  match md:
    case MB{run}:
      MB{NR.reserve(run, n)}
    case MS{s, qs, ql, c}:
      MS{s, qs, ql, c}

def feed.room(+o: B.Opts, md: Md, src: List<&1, Src>, r: D.Bytes & U32, pend: Pd, eof: Bool, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  (b, +n) = r
  feed.k(o, md.reserve(md, n), src, b, Pd.len(pend), eof, back, win, asked, fneed, dfs)

# A piece of the VCF file: its lines are read in place; the end of a line
# left from the last piece is joined with this piece's first line.
def feed(st: St, b: D.Bytes) -> St:
  match st:
    case St{+o, md, src, pend, eof, +back, win, asked, +fneed, dfs}:
      feed.room(o, md, src, BY.len(b), pend, eof, back, win, asked, fneed, dfs)

# The last line, without an LF: given one (its text as B.Text.last has it).
def eof_src(pd: Pd) -> Src:
  match pd:
    case PB{b}:
      SB{NR.put_str(b, "\n"), 0}
    case PS{s}:
      SL{s}

def feed_eof.if(empty: Bool, +o: B.Opts, md: Md, src: List<&1, Src>, pend: Pd, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  match empty:
    case True{}:
      St{o, md, src, pend, True{}, back, win, asked, fneed, dfs}
    case False{}:
      St{o, md, List.append(&1, Src, src, [eof_src(pend)]), PB{BY.empty(0n)}, True{}, back, win, asked, fneed, dfs}

def feed_eof.k(+o: B.Opts, md: Md, src: List<&1, Src>, r: Pd & Nat, +back: Nat, win: Win, asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, dfs: B.Defs) -> St:
  (pend, +n) = r
  feed_eof.if(Nat.is_eq(n, 0n), o, md, src, pend, back, win, asked, fneed, dfs)

# The end of the file: what is left after the last LF is the last line.
def feed_eof(st: St) -> St:
  match st:
    case St{+o, md, src, pend, eof, +back, win, asked, +fneed, dfs}:
      feed_eof.k(o, md, src, Pd.len(pend), back, win, asked, fneed, dfs)

def set_win.of(asked: Maybe<&2, List<&2, P.Req>>, win: Win, as: List<&1, P.Ans>) -> Win:
  match asked:
    case None{}:
      win
    case Some{rs}:
      win_of(rs, as)

# The answers to the reads asked last, kept (after an empty Ask, the last
# answer stays).
def set_win(st: St, as: List<&1, P.Ans>) -> St:
  match st:
    case St{o, md, src, pend, eof, back, win, asked, fneed, dfs}:
      St{o, md, src, pend, eof, back, set_win.of(asked, win, as), None{}, fneed, dfs}

# One step of the program.
def step(st: St, i: P.In) -> Step:
  match i:
    case P.Chunk{b}:
      go(feed(st, b))
    case P.Eof{}:
      go(feed_eof(st))
    case P.Ref{as}:
      go(set_win(st, as))

# A hit (for the proofs).
def Wr.hit(w: Wr) -> Bool:
  match w:
    case WHit{}:
      True{}
    case _:
      False{}

def Cut2.now(c: Cut2) -> String:
  match c:
    case Cut2{n, l}:
      n

def Cut2.later(c: Cut2) -> String:
  match c:
    case Cut2{n, l}:
      l
