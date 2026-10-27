import Base
import ./types.bend as B
import ./run.bend as R

# framebender: the normalizer (code, not spec). LAWS.bend states what it must do.

# ---------------------------------------------------------------------------
# Reading the reference through a window
# ---------------------------------------------------------------------------

def Win.get.if(below: Bool, bases: List<&2, B.Base>, off: Nat, i: Nat) -> Maybe<&2, B.Base>:
  match below:
    case True{}:
      None{}
    case False{}:
      List.get(&2, B.Base, bases, Nat.sub(i, off))

# The base at 0-based contig index i, or None when the window does not hold it.
def Win.get(+off: Nat, bases: List<&2, B.Base>, +i: Nat) -> Maybe<&2, B.Base>:
  Win.get.if(Nat.is_lt(i, off), bases, off, i)

# ---------------------------------------------------------------------------
# Tan et al.'s algorithm on all alleles at once (REF first, then the ALTs):
# trim or shift from the right, then trim the left
# ---------------------------------------------------------------------------

type Act is Data:
  AStop{}
  ATrim{}
  AShift{b: B.Base}
  ANeed{}

# Alleles REF, ALT1, ALT2, ... being normalized, at position pos.
type Cur is Data:
  Cur{pos: Nat, als: List<&2, List<&2, B.Base>>}

def opt_eq(a: Maybe<&2, B.Base>, b: Maybe<&2, B.Base>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      B.Base.is_eq(x, y)
    case _ _:
      False{}

def same_last(+x: Maybe<&2, B.Base>, als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case a <> t:
      opt_eq(x, List.last(&2, B.Base, a)) && same_last(x, t)

# Every allele ends with the same base.
def lasts_eq(als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      False{}
    case a <> t:
      same_last(List.last(&2, B.Base, a), t)

def same_first(+x: Maybe<&2, B.Base>, als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case a <> t:
      opt_eq(x, List.head(&2, B.Base, a)) && same_first(x, t)

# Every allele starts with the same base.
def firsts_eq(als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      False{}
    case a <> t:
      same_first(List.head(&2, B.Base, a), t)

# Every allele has at least two bases.
def all_long(als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case a <> t:
      Nat.is_le(2n, List.length(&2, B.Base, a)) && all_long(t)

def init(+xs: List<&2, B.Base>) -> List<&2, B.Base>:
  List.take(&2, B.Base, xs, Nat.sub(List.length(&2, B.Base, xs), 1n))

def inits(als: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case a <> t:
      init(a) <> inits(t)

def tails(als: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case a <> t:
      List.tail(&2, B.Base, a) <> tails(t)

# b put in front of every allele, which loses its last base.
def shifted(+b: B.Base, als: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case a <> t:
      {b <> init(a) : List<&2, B.Base>} <> shifted(b, t)

def next_act.if(eq: Bool, long: Bool, shift: Bool, b: Maybe<&2, B.Base>) -> Act:
  match eq:
    case False{}:
      AStop{}
    case True{}:
      match long:
        case True{}:
          ATrim{}
        case False{}:
          match shift:
            case False{}:
              AStop{}
            case True{}:
              match b:
                case None{}:
                  ANeed{}
                case Some{x}:
                  AShift{x}

# The next step: when the alleles all end with the same base, trim it if every
# allele is long enough, else move one base left (taking the base before pos
# as the new first base) unless pos is 1. Need: that base is outside the window.
def next_act(+off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +als: List<&2, List<&2, B.Base>>) -> Act:
  next_act.if(lasts_eq(als), all_long(als), Nat.is_le(2n, pos), Win.get(off, bases, Nat.sub(pos, 2n)))

def right(fuel: Nat, act: Act, +off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +als: List<&2, List<&2, B.Base>>) -> Maybe<&2, Cur>:
  match fuel:
    case 0n:
      Some{Cur{pos, als}}
    case 1n+f:
      match act:
        case AStop{}:
          Some{Cur{pos, als}}
        case ANeed{}:
          None{}
        case ATrim{}:
          +a = inits(als)
          right(f, next_act(off, bases, pos, a), off, bases, pos, a)
        case AShift{+b}:
          +p = Nat.sub(pos, 1n)
          +a = shifted(b, als)
          right(f, next_act(off, bases, p, a), off, bases, p, a)

def left(fuel: Nat, go: Bool, +pos: Nat, +als: List<&2, List<&2, B.Base>>) -> Cur:
  match fuel:
    case 0n:
      Cur{pos, als}
    case 1n+f:
      match go:
        case False{}:
          Cur{pos, als}
        case True{}:
          +a = tails(als)
          left(f, firsts_eq(a) && all_long(a), 1n+pos, a)

def to_var(c: Cur) -> B.Var:
  match c:
    case Cur{p, r <> t}:
      B.Var{p, r, t}
    case Cur{p, Nil{}}:
      B.Var{p, Nil{}, Nil{}}

def total(als: List<&2, List<&2, B.Base>>) -> Nat:
  match als:
    case Nil{}:
      0n
    case a <> t:
      Nat.add(List.length(&2, B.Base, a), total(t))

def left_of(m: Maybe<&2, Cur>) -> Maybe<&2, B.Var>:
  match m:
    case None{}:
      None{}
    case Some{Cur{+p, +a}}:
      Some{to_var(left(Nat.add(p, total(a)), firsts_eq(a) && all_long(a), p, a))}

# The normalized variant, or None when the window is too small to tell.
def var_in(+off: Nat, +bases: List<&2, B.Base>, v: B.Var) -> Maybe<&2, B.Var>:
  match v:
    case B.Var{+pos, ref, alts}:
      +als = {ref <> alts : List<&2, List<&2, B.Base>>}
      fuel = Nat.add(pos, total(als))
      left_of(right(fuel, next_act(off, bases, pos, als), off, bases, pos, als))

def var(+seq: List<&2, B.Base>, +v: B.Var) -> B.Var:
  Maybe.default(&2, B.Var, var_in(0n, seq, v), v)

# ---------------------------------------------------------------------------
# One body line, reading the contig through what the reference answered
# ---------------------------------------------------------------------------

def mk(o: B.Outcome, +fs: List<&2, String>, body: String) -> B.Res:
  B.Res{o, B.Rec.pos(fs), body, False{}}

def found.norm(m: Maybe<&2, B.Var>, +fs: List<&2, String>, +v: B.Var) -> Maybe<&2, B.Res>:
  match m:
    case None{}:
      None{}
    case Some{+w}:
      Some{B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(fs, v, w), B.Rec.stale(fs, v, w)}}

def ref_check.go(fits: Bool, covered: Bool, eq: Bool) -> Maybe<&2, Bool>:
  match fits covered:
    case False{} _:
      Some{False{}}
    case True{} False{}:
      None{}
    case True{} True{}:
      Some{eq}

# The REF check through the window: Some(True) matches, Some(False) does not
# (also when REF runs past the contig end), None: the window does not hold it.
def ref_check(+clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +start: Nat, +ref: List<&2, B.Base>) -> Maybe<&2, Bool>:
  +n = List.length(&2, B.Base, ref)
  +fits = Nat.is_le(Nat.add(start, n), clen)
  +covered = Nat.is_le(off, start) && Nat.is_le(Nat.add(start, n), Nat.add(off, List.length(&2, B.Base, bases)))
  ref_check.go(fits, covered, B.Bases.eq(List.take(&2, B.Base, List.drop(&2, B.Base, bases, Nat.sub(start, off)), n), ref))

def found.ref(ok: Maybe<&2, Bool>, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String, +v: B.Var) -> Maybe<&2, B.Res>:
  match ok:
    case None{}:
      None{}
    case Some{False{}}:
      Some{mk(B.Problem{B.RefMismatch{}}, fs, body)}
    case Some{True{}}:
      found.norm(var_in(off, bases, v), fs, v)

def found.problem(zero: Bool, distinct: Bool, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String, +v: B.Var) -> Maybe<&2, B.Res>:
  match zero distinct:
    case True{} _:
      Some{mk(B.Problem{B.BadPos{}}, fs, body)}
    case False{} False{}:
      Some{mk(B.Problem{B.AltDup{}}, fs, body)}
    case False{} True{}:
      match v:
        case B.Var{+p, +r, +a}:
          found.ref(ref_check(clen, off, bases, Nat.sub(p, 1n), r), off, bases, fs, body, B.Var{p, r, a})

def found.var(+clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String, +v: B.Var) -> Maybe<&2, B.Res>:
  match v:
    case B.Var{+p, +r, +a}:
      found.problem(Nat.is_eq(p, 0n), B.Alleles.distinct(r <> a), clen, off, bases, fs, body, B.Var{p, r, a})

def found(end_ok: Bool, r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match end_ok r a:
    case False{} _ _:
      Some{mk(B.Problem{B.BadEnd{}}, fs, body)}
    case True{} Some{ref} Some{alts}:
      found.var(clen, off, bases, fs, body, B.Var{B.Rec.pos(fs), ref, alts})
    case True{} _ _:
      Some{mk(B.Problem{B.NonAcgtn{}}, fs, body)}

def judge_in.ans(a: B.Ans, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match a:
    case B.NoAns{}:
      None{}
    case B.Unknown{}:
      Some{mk(B.NoContig{}, fs, body)}
    case B.Known{+clen, +off, raw}:
      +bases = B.Bases.of_fasta(raw)
      +ref = B.Rec.field(fs, 3n)
      e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      found(B.Info.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), clen, off, bases, fs, body)

def judge_in.go(bad: Bool, skip: Bool, a: B.Ans, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match bad skip:
    case True{} _:
      Some{mk(B.Broken{}, fs, body)}
    case False{} True{}:
      Some{mk(B.Skipped{}, fs, body)}
    case False{} False{}:
      judge_in.ans(a, fs, body)

# The result for one body line (its text without terminator), given what the
# reference answered for the line's CHROM; None when the answer is not enough
# (the machine then asks for more).
def judge_in(a: B.Ans, +body: String) -> Maybe<&2, B.Res>:
  +fs = B.Rec.fields(body)
  judge_in.go(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), a, fs, body)

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
