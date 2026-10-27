import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_var.bend as V
import ./norm_line.bend as J

# framebender: the program (code, not spec). LAWS.bend states what it must do.
# The laws reach the code through Norm.var, Norm.judge_in, Norm.start and
# Norm.step.

# The normalized variant (norm_var.bend).
def var(+seq: List<&2, B.Base>, +v: B.Var) -> B.Var:
  V.var(seq, v)

# The result for one body line through a reference answer (norm_line.bend).
def judge_in(a: B.Ans, +body: String) -> Maybe<&2, B.Res>:
  J.judge_in(a, body)

# ---------------------------------------------------------------------------
# The program as a state machine
# ---------------------------------------------------------------------------

# A body line waiting for a reference read; the window starts back letters
# before its POS.
type Pending is Data:
  Pending{line: B.Line, back: Nat}

# The machine's state: the options; the run's bookkeeping (R.RunSt, shared
# with the spec; its out and notes are emptied after every line); the end of
# a line not yet complete; complete lines not yet handled; whether the file
# ended; the line waiting for a reference read.
type St is Data:
  St{o: B.Opts, rs: R.RunSt, pend: String, queue: List<&2, B.Line>, eof: Bool, wait: Maybe<&2, Pending>}

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
      Begin{St{o, R.start_st(), "", Nil{}, False{}, None{}}, r, v}

# The command line after the program's name.
def start(argv: List<&2, String>) -> Begin:
  start.of(B.Args.parse(argv))

# One step: the new state, bytes for stdout, messages for stderr, what next.
type Step is Data:
  Step{st: St, out: String, notes: List<&2, B.Note>, next: B.Next}

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

def went(+o: B.Opts, +rs: R.RunSt, pend: String, queue: List<&2, B.Line>, eof: Bool) -> Adv:
  Went{St{o, RunSt.clear(rs), pend, queue, eof, None{}}, RunSt.out(rs), RunSt.notes(rs)}

def body_done(r: B.Res, +o: B.Opts, rs: R.RunSt, +l: B.Line, pend: String, queue: List<&2, B.Line>, eof: Bool) -> Adv:
  +fs = B.Rec.fields(B.Line.body(l))
  +rs1 = R.tick(rs)
  +at = {B.At{R.RunSt.n(rs1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
  went(o, R.body_line(r, rs1, o, l, at, B.Rec.pos(fs)), pend, queue, eof)

# The window asked for a line: from back letters before its POS to the end of
# its REF.
def want(+o: B.Opts, +rs: R.RunSt, +l: B.Line, +back: Nat, pend: String, queue: List<&2, B.Line>, eof: Bool) -> Adv:
  +fs = B.Rec.fields(B.Line.body(l))
  +p = Nat.sub(B.Rec.pos(fs), 1n)
  Want{St{o, rs, pend, queue, eof, Some{Pending{l, back}}}, B.Rec.field(fs, 0n), Nat.sub(p, back), Nat.add(p, String.length(B.Rec.field(fs, 3n)))}

def try_line(m: Maybe<&2, B.Res>, +o: B.Opts, +rs: R.RunSt, +l: B.Line, +back: Nat, +pend: String, +queue: List<&2, B.Line>, +eof: Bool) -> Adv:
  match m:
    case Some{r}:
      body_done(r, o, rs, l, pend, queue, eof)
    case None{}:
      want(o, rs, l, back, pend, queue, eof)

def next_line(inbody: Bool, +o: B.Opts, +rs: R.RunSt, +l: B.Line, +pend: String, +queue: List<&2, B.Line>, +eof: Bool) -> Adv:
  match inbody:
    case False{}:
      went(o, R.head_line(R.is_chrom_line(B.Line.body(l)), R.tick(rs), o, l), pend, queue, eof)
    case True{}:
      try_line(judge_in(B.NoAns{}, B.Line.body(l)), o, rs, l, 100n, pend, queue, eof)

def advance.go(halted: Bool, st: St) -> Adv:
  match halted st:
    case True{} _:
      Ended{st}
    case False{} St{o, +rs, pend, Nil{}, eof, w}:
      Idle{St{o, rs, pend, Nil{}, eof, w}}
    case False{} St{o, +rs, pend, l <> t, eof, w}:
      next_line(R.RunSt.inbody(rs), o, rs, l, pend, t, eof)

def St.rs(st: St) -> R.RunSt:
  match st:
    case St{o, rs, p, q, e, w}:
      rs

# Handle the next complete line, if any.
def advance(+st: St) -> Adv:
  advance.go(R.RunSt.halt(St.rs(st)), st)

# A reference read arrived for the waiting line: handle the line, or ask
# again with a window twice as far back.
def resolve(st: St, a: B.Ans) -> Adv:
  match st:
    case St{o, rs, pend, queue, eof, None{}}:
      advance(St{o, rs, pend, queue, eof, None{}})
    case St{o, rs, pend, queue, eof, Some{Pending{+l, +back}}}:
      try_line(judge_in(a, B.Line.body(l)), o, rs, l, Nat.add(Nat.mul(back, 2n), 1n), pend, queue, eof)

def rev_onto(xs: List<&2, B.Note>, acc: List<&2, B.Note>) -> List<&2, B.Note>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_onto(t, x <> acc)

def outs_text(outs: List<&2, String>) -> String:
  String.concat(List.reverse(&2, String, outs))

def notes_list(ns: List<&2, B.Note>) -> List<&2, B.Note>:
  List.reverse(&2, B.Note, ns)

def finish.of(rep: R.Report, st: St, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  match rep:
    case R.Report{out, notes, code}:
      Step{st, outs_text(outs) ++ out, List.append(&2, B.Note, notes_list(ns), notes), B.Finish{code}}

# The end of the run: the buffer is written (R.finish) and the program stops.
def finish(+st: St, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  finish.of(R.finish(St.rs(st)), st, outs, ns)

def St.eof(st: St) -> Bool:
  match st:
    case St{o, rs, p, q, e, w}:
      e

def idle(eof: Bool, st: St, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  match eof:
    case True{}:
      finish(st, outs, ns)
    case False{}:
      Step{st, outs_text(outs), notes_list(ns), B.More{}}

# Handle lines until one needs the reference, none is left, or the run stops.
# outs and ns collect what was written, newest first.
def pump(fuel: Nat, a: Adv, outs: List<&2, String>, ns: List<&2, B.Note>) -> Step:
  match fuel a:
    case 0n Went{st, o, n}:
      Step{st, outs_text(o <> outs), notes_list(rev_onto(n, ns)), B.More{}}
    case 0n Want{st, c, f, u}:
      Step{st, outs_text(outs), notes_list(ns), B.Ask{c, f, u}}
    case 0n Idle{st}:
      Step{st, outs_text(outs), notes_list(ns), B.More{}}
    case 0n Ended{st}:
      finish(st, outs, ns)
    case 1n+f Went{+st, o, n}:
      pump(f, advance(st), o <> outs, rev_onto(n, ns))
    case 1n+f Want{st, c, fr, u}:
      Step{st, outs_text(outs), notes_list(ns), B.Ask{c, fr, u}}
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

def feed.go(ps: List<&2, String>, p: String) -> Fed:
  match ps:
    case Nil{}:
      Fed{Nil{}, p}
    case q <> t:
      Fed.cons(B.Text.line(p), feed.go(t, q))

def feed.start(ps: List<&2, String>) -> Fed:
  match ps:
    case Nil{}:
      Fed{Nil{}, ""}
    case p <> t:
      feed.go(t, p)

def feed.put(f: Fed, st: St) -> St:
  match f st:
    case Fed{ls, r} St{o, rs, p, q, e, w}:
      St{o, rs, r, List.append(&2, B.Line, q, ls), e, w}

# A piece of the VCF file: the complete lines go to the queue.
def feed(st: St, s: String) -> St:
  match st:
    case St{o, rs, p, q, e, w}:
      feed.put(feed.start(String.split(p ++ s, '\n')), St{o, rs, "", q, e, w})

# The end of the file: what is left after the last LF is the last line.
def feed_eof(st: St) -> St:
  match st:
    case St{o, rs, p, q, e, w}:
      St{o, rs, "", List.append(&2, B.Line, q, B.Text.last(p)), True{}, w}

def St.fuel(st: St) -> Nat:
  match st:
    case St{o, rs, p, q, e, w}:
      Nat.add(List.length(&2, B.Line, q), 2n)

def step.go(+st: St, a: Adv) -> Step:
  pump(St.fuel(st), a, Nil{}, Nil{})

# One step of the program.
def step(st: St, i: B.In) -> Step:
  match i:
    case B.Chunk{s}:
      +st2 = feed(st, s)
      step.go(st2, advance(st2))
    case B.Eof{}:
      +st2 = feed_eof(st)
      step.go(st2, advance(st2))
    case B.Ref{a}:
      +st2 = st
      step.go(st2, resolve(st2, a))
