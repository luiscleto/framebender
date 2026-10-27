import Base
import ./types.bend as B

# framebender: how a run handles lines, one at a time (spec).
#
# Part of the spec, split out of LAWS.bend unchanged (2026-10-27) so that the
# code can use the same bookkeeping: LAWS.run feeds it the outcome of
# LAWS.judge for each line, the machine (norm.bend) the outcome of
# Norm.judge_in. Reviewed and approved with LAWS.bend.

def version() -> String:
  "0.1.0"

def clean.char(c: Char) -> Char:
  match c:
    case Chr{+x}:
      Bool.pick(Char, U32.is_lt(x, 32) || U32.is_eq(x, 127), ' ', Chr{x})

# An argument with every control character (bytes 0-31 and 127) replaced by a
# space, so the header line stays one line.
def clean(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{clean.char(h), clean(t)}

def args_text(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      " " ++ clean(x) ++ args_text(t)

# The two lines added to the header, just before the #CHROM line, ending as
# the #CHROM line ends. No date, so the output is the same on every run.
def added(o: B.Opts, +term: String) -> String:
  match o:
    case B.Opts{s, w, args}:
      "##framebender_normVersion=" ++ version() ++ term ++ "##framebender_normCommand=norm" ++ args_text(args) ++ term

# The column-header line: its first field is exactly "#CHROM".
def is_chrom_line(body: String) -> Bool:
  String.eq(B.Rec.field(B.Rec.fields(body), 0n), "#CHROM")

# A body line waiting to be written: the position it is sorted by, its input
# POS, where it came from, and its text (with terminator).
type Item is Data:
  Item{key: Nat, inpos: Nat, at: B.At, text: String}

def Item.key(i: Item) -> Nat:
  match i:
    case Item{k, p, a, t}:
      k

def Item.chrom(i: Item) -> String:
  match i:
    case Item{k, p, B.At{n, c, q}, t}:
      c

def Item.inpos(i: Item) -> Nat:
  match i:
    case Item{k, p, a, t}:
      p

def Item.text(i: Item) -> String:
  match i:
    case Item{k, p, a, t}:
      t

def Item.at(i: Item) -> B.At:
  match i:
    case Item{k, p, a, t}:
      a

def insert.put(le: Bool, +x: Item, +e: Item, +t: List<&2, Item>, ins: List<&2, Item>) -> List<&2, Item>:
  match le:
    case True{}:
      x <> ins
    case False{}:
      e <> x <> t

# Insert e after every item whose key is at most e's (so equal keys keep their
# input order).
def insert(+e: Item, buf: List<&2, Item>) -> List<&2, Item>:
  match buf:
    case Nil{}:
      [e]
    case +x <> +t:
      insert.put(Nat.is_le(Item.key(x), Item.key(e)), x, e, t, insert(e, t))

def ready(+w: Nat, +inpos: Nat, x: Item) -> Bool:
  Nat.is_le(Nat.add(Item.key(x), w), inpos)

def take_ready.put(ok: Bool, x: Item, rest: List<&2, Item>) -> List<&2, Item>:
  match ok:
    case True{}:
      x <> rest
    case False{}:
      Nil{}

# The items at the front of the buffer that are ready: key + w <= inpos.
def take_ready(+w: Nat, +inpos: Nat, buf: List<&2, Item>) -> List<&2, Item>:
  match buf:
    case Nil{}:
      Nil{}
    case +x <> t:
      take_ready.put(ready(w, inpos, x), x, take_ready(w, inpos, t))

def drop_ready.put(ok: Bool, x: Item, t: List<&2, Item>, rest: List<&2, Item>) -> List<&2, Item>:
  match ok:
    case True{}:
      rest
    case False{}:
      x <> t

# The buffer without take_ready's items.
def drop_ready(+w: Nat, +inpos: Nat, buf: List<&2, Item>) -> List<&2, Item>:
  match buf:
    case Nil{}:
      Nil{}
    case +x <> +t:
      drop_ready.put(ready(w, inpos, x), x, t, drop_ready(w, inpos, t))

# Writing items in order: all of them, with the last item written; or the
# writing stops at the first item whose key is below the last key written
# (bad), naming the item written before it (prev).
type Flush is Data:
  Flushed{out: String, last: Maybe<&2, Item>}
  Broke{out: String, bad: B.At, prev: Maybe<&2, B.At>}

def Flush.pre(s: String, f: Flush) -> Flush:
  match f:
    case Flushed{o, l}:
      Flushed{s ++ o, l}
    case Broke{o, b, p}:
      Broke{s ++ o, b, p}

def at_of(m: Maybe<&2, Item>) -> Maybe<&2, B.At>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{Item.at(x)}

def flush.put(ok: Bool, +x: Item, last: Maybe<&2, Item>, rest: Flush) -> Flush:
  match ok:
    case True{}:
      Flush.pre(Item.text(x), rest)
    case False{}:
      Broke{"", Item.at(x), at_of(last)}

def flush.ok(last: Maybe<&2, Item>, +k: Nat) -> Bool:
  match last:
    case None{}:
      True{}
    case Some{l}:
      Nat.is_le(Item.key(l), k)

def flush(items: List<&2, Item>, +last: Maybe<&2, Item>) -> Flush:
  match items:
    case Nil{}:
      Flushed{"", last}
    case +x <> t:
      flush.put(flush.ok(last, Item.key(x)), x, last, flush(t, Some{x}))

# Counts for the summary: body lines, changed, out of scope, passed through
# with a problem.
type Cnt is Data:
  Cnt{lines: Nat, changed: Nat, skipped: Nat, warned: Nat}

# The state of a run after some lines.
#   n: lines read; inbody: the #CHROM line was read; head: the header lines
#   before it; cur: the current CHROM run; ended: CHROMs whose run ended;
#   last: the last item written in the current run; buf: items waiting, sorted
#   by key; out: bytes written; notes: messages so far; halt: the run stopped.
type RunSt is Data:
  RunSt{n: Nat, inbody: Bool, head: String, cur: Maybe<&2, String>, ended: List<&2, String>, last: Maybe<&2, Item>, buf: List<&2, Item>, cnt: Cnt, out: String, notes: List<&2, B.Note>, halt: Bool}

def has(+s: String, ss: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case t <> rest:
      String.eq(s, t) || has(s, rest)

def RunSt.n(st: RunSt) -> Nat:
  match st:
    case RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      n

def stop(st: RunSt, +out: String, nt: B.Note) -> RunSt:
  match st:
    case RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      RunSt{n, i, h, c, e, l, b, k, o ++ out, List.append(&2, B.Note, ns, [nt]), True{}}

def emit.ready(f: Flush, st: RunSt, rest: List<&2, Item>, +at: B.At) -> RunSt:
  match f st:
    case Broke{o, bad, prev} _:
      stop(st, o, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case Flushed{o2, l2} RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      RunSt{n, i, h, c, e, l2, rest, k, o ++ o2, ns, x}

# Same CHROM run: insert the item, then write the ready items.
def same_run(st: RunSt, +w: Nat, +it: Item) -> RunSt:
  match st:
    case RunSt{n, i, h, c, e, +l, b, k, o, ns, x}:
      match it:
        case Item{+key, +inpos, +at, +text}:
          +buf = insert(Item{key, inpos, at, text}, b)
          emit.ready(flush(take_ready(w, inpos, buf), l), RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x}, drop_ready(w, inpos, buf), at)

def push_cur(c: Maybe<&2, String>, e: List<&2, String>) -> List<&2, String>:
  match c:
    case None{}:
      e
    case Some{s}:
      s <> e

def new_run.go(f: Flush, again: Bool, st: RunSt, +w: Nat, +chrom: String, +it: Item) -> RunSt:
  match f again st:
    case Broke{o, bad, prev} _ _:
      stop(st, o, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case Flushed{o2, l2} True{} _:
      stop(st, o2, B.Stop{B.Unsorted{}, Some{Item.at(it)}, None{}})
    case Flushed{o2, l2} False{} RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      same_run(RunSt{n, i, h, Some{chrom}, push_cur(c, e), None{}, Nil{}, k, o ++ o2, ns, x}, w, it)

# A new CHROM: write the whole buffer; if this CHROM's run already ended, stop
# with UNSORTED; else start its run.
def new_run(st: RunSt, +w: Nat, +chrom: String, +it: Item) -> RunSt:
  match st:
    case RunSt{n, i, h, c, +e, +l, +b, k, o, ns, x}:
      new_run.go(flush(b, l), has(chrom, e), RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)

def is_cur(c: Maybe<&2, String>, +chrom: String) -> Bool:
  match c:
    case None{}:
      False{}
    case Some{s}:
      String.eq(s, chrom)

def keyed.go(same: Bool, +st2: RunSt, +w: Nat, +chrom: String, +it: Item) -> RunSt:
  match same:
    case True{}:
      same_run(st2, w, it)
    case False{}:
      new_run(st2, w, chrom, it)

# A line that goes on (not stopping the run): its messages first, then the
# CHROM-run rule, then the buffer rule.
def keyed(st: RunSt, +w: Nat, +it: Item, nts: List<&2, B.Note>, k2: Cnt) -> RunSt:
  match st:
    case RunSt{n, i, h, +c, e, l, b, k, o, ns, x}:
      +chrom = Item.chrom(it)
      +st2 = {RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x} : RunSt}
      keyed.go(is_cur(c, chrom), st2, w, chrom, it)

def bump(c: Cnt, changed: Bool, skipped: Bool, warned: Bool) -> Cnt:
  match c:
    case Cnt{n, ch, sk, wa}:
      Cnt{1n+n, Nat.add(ch, Bool.pick(Nat, changed, 1n, 0n)), Nat.add(sk, Bool.pick(Nat, skipped, 1n, 0n)), Nat.add(wa, Bool.pick(Nat, warned, 1n, 0n))}

def RunSt.cnt(st: RunSt) -> Cnt:
  match st:
    case RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      k

def stale_note(s: Bool, +at: B.At) -> List<&2, B.Note>:
  Bool.pick(List<&2, B.Note>, s, [B.Warning{B.Stale{}, at}], Nil{})

def Opts.w(o: B.Opts) -> Nat:
  match o:
    case B.Opts{s, w, a}:
      w

def Opts.strict(o: B.Opts) -> Bool:
  match o:
    case B.Opts{s, w, a}:
      s

def problem_line(strict: Bool, +st: RunSt, +w: Nat, +c: B.Code, +l: B.Line, +at: B.At, +inpos: Nat) -> RunSt:
  match strict:
    case True{}:
      stop(st, "", B.Stop{c, Some{at}, None{}})
    case False{}:
      keyed(st, w, Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}], bump(RunSt.cnt(st), False{}, False{}, True{}))

# One body line, by its outcome: MALFORMED and UNKNOWN_CHROM stop the run; a
# problem stops it under -c e and is passed through with a warning under -c w;
# out of scope is passed through; normalized is written in normal form.
def body_line(r: B.Res, +st: RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat) -> RunSt:
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      stop(st, "", B.Stop{B.Malformed{}, Some{at}, None{}})
    case B.Res{B.NoContig{}, k, t, s}:
      stop(st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}})
    case B.Res{B.Problem{+c}, k, t, s}:
      problem_line(Opts.strict(o), st, Opts.w(o), c, l, at, inpos)
    case B.Res{B.Skipped{}, k, t, s}:
      keyed(st, Opts.w(o), Item{inpos, inpos, at, B.Line.text(l)}, Nil{}, bump(RunSt.cnt(st), False{}, True{}, False{}))
    case B.Res{B.Normalized{}, k, +t, s}:
      keyed(st, Opts.w(o), Item{k, inpos, at, t ++ B.Line.term(l)}, stale_note(s, at), bump(RunSt.cnt(st), Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))

def head_line(isc: Bool, st: RunSt, o: B.Opts, l: B.Line) -> RunSt:
  match isc st l:
    case True{} RunSt{n, i, h, c, e, la, b, k, out, ns, x} B.Line{+bd, +term}:
      RunSt{n, True{}, "", c, e, la, b, k, h ++ added(o, term) ++ bd ++ term, ns, x}
    case False{} RunSt{n, i, h, c, e, la, b, k, out, ns, x} _:
      RunSt{n, i, h ++ B.Line.text(l), c, e, la, b, k, out, ns, x}

def tick(st: RunSt) -> RunSt:
  match st:
    case RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      RunSt{1n+n, i, h, c, e, l, b, k, o, ns, x}

def RunSt.inbody(st: RunSt) -> Bool:
  match st:
    case RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      i

def RunSt.halt(st: RunSt) -> Bool:
  match st:
    case RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      x

# What a run produces: the bytes on stdout, the messages on stderr (each
# written as B.Note.render gives), and the exit code.
type Report is Data:
  Report{out: String, notes: List<&2, B.Note>, code: Nat}

def Report.out(r: Report) -> String:
  match r:
    case Report{o, n, c}:
      o

def Report.notes(r: Report) -> List<&2, B.Note>:
  match r:
    case Report{o, n, c}:
      n

def Report.code(r: Report) -> Nat:
  match r:
    case Report{o, n, c}:
      c

def finish.flush(f: Flush, +o: String, +ns: List<&2, B.Note>, k: Cnt) -> Report:
  match f k:
    case Broke{o2, bad, prev} _:
      Report{o ++ o2, List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), 1n}
    case Flushed{o2, l2} Cnt{n, ch, sk, wa}:
      Report{o ++ o2, List.append(&2, B.Note, ns, [B.Summary{n, ch, sk, wa}]), 0n}

# The end of the file: a run that stopped ends with exit code 1; a file without
# a #CHROM line is an error (NO_HEADER, nothing written); else the buffer is
# written and the run ends with the summary and exit code 0.
def finish(st: RunSt) -> Report:
  match st:
    case RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      match i x:
        case _ True{}:
          Report{o, ns, 1n}
        case False{} False{}:
          Report{"", [B.Stop{B.NoHeader{}, None{}, None{}}], 1n}
        case True{} False{}:
          finish.flush(flush(b, l), o, ns, k)

def start_st() -> RunSt:
  RunSt{0n, False{}, "", None{}, Nil{}, None{}, Nil{}, Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}
