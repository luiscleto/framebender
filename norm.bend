import Base
import ./types.bend as B
import ./protocol.bend as P
import ./run.bend as R
import ./norm_line.bend as J
import ./norm_run.bend as NR

# framebender: the program (code, not spec). MACHINE.bend states what it must
# do; the law reaches the code through Norm.start and Norm.step.

# The result for one body line through a reference answer (norm_line.bend).
def judge_in(a: Maybe<&2, P.Ans>, +body: String) -> Maybe<&2, B.Res>:
  J.judge_in(a, body)

# ---------------------------------------------------------------------------
# The program as a state machine
# ---------------------------------------------------------------------------

# A body line waiting for a reference read; the window starts back letters
# before its POS; fs: its first fields (J.pfs of its body), kept so they are
# cut only once.
type Pending is Data:
  Pending{line: B.Line, back: Nat, fs: List<&2, String>}

# The machine's state: the options; the run's bookkeeping (R.RunSt, shared
# with the spec; its out and notes are emptied after every line); the end of
# a line not yet complete; complete lines not yet handled, and how many (so a
# step's fuel needs no walk of the queue); whether the file ended; the line
# waiting for a reference read.
type St is Data:
  St{o: B.Opts, rs: R.RunSt, pend: String, queue: List<&2, B.Line>, qn: Nat, eof: Bool, wait: Maybe<&2, Pending>}

# How the program starts: with the state and the paths of the FASTA and VCF
# files, or with a usage error.
type Begin is Data:
  Begin{st: St, ref: String, vcf: String}
  Usage{}

def start.of(m: Maybe<&2, B.Cfg>) -> Begin:
  match m:
    case None{}:
      Usage{}
    case Some{B.Cfg{o, r, v}}:
      Begin{St{o, R.start_st(), "", Nil{}, 0n, False{}, None{}}, r, v}

# The command line after the program's name.
def start(argv: List<&2, String>) -> Begin:
  start.of(B.Args.parse(argv))

# One step: the new state, bytes for stdout, messages for stderr, what next.
type Step is Data:
  Step{st: St, out: String, notes: List<&2, B.Note>, next: P.Next}

# What handling the next line led to.
#   Went: a line was handled, writing out and notes.
#   Want: the line needs the reference letters of chrom from .. upto - 1.
#   Idle: no complete line is left.
#   Ended: the run has stopped.
type Adv is Data:
  Went{st: St, out: String, notes: List<&2, B.Note>}
  Want{st: St, chrom: String, from: Nat, upto: Nat}
  Idle{st: St}
  Ended{st: St}

def RunSt.out(rs: R.RunSt) -> String:
  match rs:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      o

def RunSt.notes(rs: R.RunSt) -> List<&2, B.Note>:
  match rs:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ns

# The bookkeeping with its out and notes emptied (they were handed on).
def RunSt.clear(rs: R.RunSt) -> R.RunSt:
  match rs:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, "", Nil{}, x}

def went(+o: B.Opts, +rs: R.RunSt, pend: String, queue: List<&2, B.Line>, qn: Nat, eof: Bool) -> Adv:
  Went{St{o, RunSt.clear(rs), pend, queue, qn, eof, None{}}, RunSt.out(rs), RunSt.notes(rs)}

# fs: the line's first fields (J.pfs of its body), cut once per visit.
def body_done(r: B.Res, +o: B.Opts, rs: R.RunSt, +l: B.Line, +fs: List<&2, String>, pend: String, queue: List<&2, B.Line>, qn: Nat, eof: Bool) -> Adv:
  +rs1 = R.tick(rs)
  +at = {B.At{R.RunSt.n(rs1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
  went(o, NR.body_line(r, rs1, o, l, at, B.Rec.pos(fs)), pend, queue, qn, eof)

# The window asked for a line: from back letters before its POS to the end of
# its REF.
def want(+o: B.Opts, +rs: R.RunSt, +l: B.Line, +fs: List<&2, String>, +back: Nat, pend: String, queue: List<&2, B.Line>, qn: Nat, eof: Bool) -> Adv:
  +p = Nat.sub(B.Rec.pos(fs), 1n)
  Want{St{o, rs, pend, queue, qn, eof, Some{Pending{l, back, fs}}}, B.Rec.field(fs, 0n), Nat.sub(p, back), Nat.add(p, String.length(B.Rec.field(fs, 3n)))}

def try_line(m: Maybe<&2, B.Res>, +o: B.Opts, +rs: R.RunSt, +l: B.Line, +fs: List<&2, String>, +back: Nat, +pend: String, +queue: List<&2, B.Line>, +qn: Nat, +eof: Bool) -> Adv:
  match m:
    case Some{r}:
      body_done(r, o, rs, l, fs, pend, queue, qn, eof)
    case None{}:
      want(o, rs, l, fs, back, pend, queue, qn, eof)

def next_line(inbody: Bool, +o: B.Opts, +rs: R.RunSt, +l: B.Line, +pend: String, +queue: List<&2, B.Line>, +qn: Nat, +eof: Bool) -> Adv:
  match inbody:
    case False{}:
      went(o, R.head_line(R.is_chrom_line(B.Line.body(l)), R.tick(rs), o, l), pend, queue, qn, eof)
    case True{}:
      +fs = J.pfs(B.Line.body(l))
      try_line(J.judge_fs(None{}, fs, B.Line.body(l)), o, rs, l, fs, 100n, pend, queue, qn, eof)

def advance.go(halted: Bool, st: St) -> Adv:
  match halted st:
    case True{} _:
      Ended{st}
    case False{} St{o, +rs, pend, Nil{}, qn, eof, w}:
      Idle{St{o, rs, pend, Nil{}, qn, eof, w}}
    case False{} St{o, +rs, pend, l <> t, 1n+m, eof, w}:
      next_line(R.RunSt.inbody(rs), o, rs, l, pend, t, m, eof)
    case False{} St{o, +rs, pend, l <> t, 0n, eof, w}:
      next_line(R.RunSt.inbody(rs), o, rs, l, pend, t, 0n, eof)

def St.rs(st: St) -> R.RunSt:
  match st:
    case St{o, rs, p, q, n, e, w}:
      rs

# Handle the next complete line, if any.
def advance(+st: St) -> Adv:
  advance.go(R.RunSt.halt(St.rs(st)), st)

def grow.if(whole: Bool, +back: Nat, +l: B.Line) -> Nat:
  match whole:
    case True{}:
      B.Rec.pos(B.Rec.fields(B.Line.body(l)))
    case False{}:
      Nat.add(Nat.mul(back, 2n), 1n)

# How far back the next window starts: twice as far, or (once the window is
# as long as the contig) back to the contig's first letter.
def grow(a: Maybe<&2, P.Ans>, +back: Nat, +l: B.Line) -> Nat:
  match a:
    case Some{P.Known{clen, off, raw}}:
      grow.if(Nat.is_le(clen, back), back, l)
    case _:
      Nat.add(Nat.mul(back, 2n), 1n)

# A record already in normal form (J.fast gives Same): written as it came,
# without rebuilding it (proof_fast.bend: the same as body_done with judge's
# result).
def same_done(+o: B.Opts, rs: R.RunSt, +l: B.Line, +fs: List<&2, String>, pend: String, queue: List<&2, B.Line>, qn: Nat, eof: Bool) -> Adv:
  +rs1 = R.tick(rs)
  +at = {B.At{R.RunSt.n(rs1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
  went(o, NR.keyed(rs1, R.Opts.w(o), R.Item{B.Rec.pos(fs), B.Rec.pos(fs), at, B.Line.text(l)}, Nil{}, R.bump(R.RunSt.cnt(rs1), False{}, False{}, False{})), pend, queue, qn, eof)

def resolve.k(f: J.Fast, +a: Maybe<&2, P.Ans>, +o: B.Opts, rs: R.RunSt, +l: B.Line, +back: Nat, +fs: List<&2, String>, pend: String, queue: List<&2, B.Line>, qn: Nat, eof: Bool) -> Adv:
  match f:
    case J.Same{}:
      same_done(o, rs, l, fs, pend, queue, qn, eof)
    case J.Other{m}:
      try_line(m, o, rs, l, fs, grow(a, back, l), pend, queue, qn, eof)

# A reference read arrived for the waiting line: handle the line, or ask
# again with a window further back (grow). fs is J.pfs of the line.
def resolve(st: St, +a: Maybe<&2, P.Ans>) -> Adv:
  match st:
    case St{o, rs, pend, queue, qn, eof, None{}}:
      advance(St{o, rs, pend, queue, qn, eof, None{}})
    case St{o, rs, pend, queue, qn, eof, Some{Pending{+l, +back, +fs}}}:
      resolve.k(J.fast(a, fs, B.Line.body(l)), a, o, rs, l, back, fs, pend, queue, qn, eof)

def rev_onto(xs: List<&2, B.Note>, acc: List<&2, B.Note>) -> List<&2, B.Note>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_onto(t, x <> acc)

def cat.go(xs: List<&2, String>, h: String) -> String:
  match xs:
    case Nil{}:
      h
    case x <> t:
      h ++ cat.go(t, x)

# String.concat, without copying the last piece (String.concat appends "" to
# it, which copies it).
def cat(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      cat.go(t, x)

def outs_text(outs: List<&2, String>) -> String:
  cat(List.reverse(&2, String, outs))

def notes_list(ns: List<&2, B.Note>) -> List<&2, B.Note>:
  List.reverse(&2, B.Note, ns)

def finish.of(rep: R.Report, st: St, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  match rep:
    case R.Report{out, notes, code}:
      Step{st, outs_text(outs) ++ out, List.append(&2, B.Note, notes_list(ns), notes), P.Finish{code}}

# The end of the run: the buffer is written (R.finish) and the program stops.
def finish(+st: St, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  finish.of(R.finish(St.rs(st)), st, outs, ns)

def St.eof(st: St) -> Bool:
  match st:
    case St{o, rs, p, q, n, e, w}:
      e

def idle(eof: Bool, st: St, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  match eof:
    case True{}:
      finish(st, outs, ns)
    case False{}:
      Step{st, outs_text(outs), notes_list(ns), P.More{}}

# Handle lines until one needs the reference, none is left, or the run stops.
# outs and ns collect what was written, newest first.
def pump(fuel: Nat, a: Adv, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  match fuel a:
    case 0n Went{st, o, n}:
      Step{st, outs_text(o <> outs), notes_list(rev_onto(n, ns)), P.More{}}
    case 0n Want{st, c, f, u}:
      Step{st, outs_text(outs), notes_list(ns), P.Ask{[P.Req{c, f, u}]}}
    case 0n Idle{st}:
      Step{st, outs_text(outs), notes_list(ns), P.More{}}
    case 0n Ended{st}:
      finish(st, outs, ns)
    case 1n+f Went{+st, o, n}:
      pump(f, advance(st), o <> outs, rev_onto(n, ns))
    case 1n+f Want{st, c, fr, u}:
      Step{st, outs_text(outs), notes_list(ns), P.Ask{[P.Req{c, fr, u}]}}
    case 1n+f Idle{+st}:
      idle(St.eof(st), st, outs, ns)
    case 1n+f Ended{st}:
      finish(st, outs, ns)

# Complete lines from text, and what is left after the last LF.
type Fed is Data:
  Fed{lines: List<&2, B.Line>, rest: String}

def Fed.cons(l: B.Line, f: Fed) -> Fed:
  match f:
    case Fed{ls, r}:
      Fed{l <> ls, r}

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

def feed.go(ps: List<&2, String>, p: String) -> Fed:
  match ps:
    case Nil{}:
      Fed{Nil{}, p}
    case q <> t:
      Fed.cons(line(p), feed.go(t, q))

def feed.start(ps: List<&2, String>) -> Fed:
  match ps:
    case Nil{}:
      Fed{Nil{}, ""}
    case p <> t:
      feed.go(t, p)

def feed.put(f: Fed, st: St) -> St:
  match f st:
    case Fed{+ls, r} St{o, rs, p, q, n, e, w}:
      St{o, rs, r, List.append(&2, B.Line, q, ls), Nat.add(n, List.length(&2, B.Line, ls)), e, w}

# A piece of the VCF file: the complete lines go to the queue.
def feed(st: St, s: String) -> St:
  match st:
    case St{o, rs, p, q, n, e, w}:
      feed.put(feed.start(String.split(p ++ s, '\n')), St{o, rs, "", q, n, e, w})

# The end of the file: what is left after the last LF is the last line.
def feed_eof(st: St) -> St:
  match st:
    case St{o, rs, p, q, n, e, w}:
      +ls = B.Text.last(p)
      St{o, rs, "", List.append(&2, B.Line, q, ls), Nat.add(n, List.length(&2, B.Line, ls)), True{}, w}

def St.fuel(st: St) -> Nat:
  match st:
    case St{o, rs, p, q, n, e, w}:
      Nat.add(n, 2n)

# The fuel is computed before the state is handled (an argument is evaluated
# before the call), so no second reference to the state is alive while lines
# are handled: matching a value that is referenced twice copies reference
# counts into all its fields, which made every line's text shared.
def step.go(fuel: Nat, st: St) -> Step:
  pump(fuel, advance(st), Nil{}, Nil{})

def step.ref(fuel: Nat, st: St, a: Maybe<&2, P.Ans>) -> Step:
  pump(fuel, resolve(st, a), Nil{}, Nil{})

# The first answer (the machine asks one read at a time).
def first(as: List<&2, P.Ans>) -> Maybe<&2, P.Ans>:
  match as:
    case Nil{}:
      None{}
    case a <> t:
      Some{a}

# One step of the program.
def step(st: St, i: P.In) -> Step:
  match i:
    case P.Chunk{s}:
      +st2 = feed(st, s)
      step.go(St.fuel(st2), st2)
    case P.Eof{}:
      +st2 = feed_eof(st)
      step.go(St.fuel(st2), st2)
    case P.Ref{as}:
      +st2 = st
      step.ref(St.fuel(st2), st2, first(as))
