import Base
import ./types.bend as B
import ./run.bend as R

# framebender: the run's bookkeeping as the machine does it (code, not spec).
# run.bend's functions (proof_fast_run.bend proves each gives blank_st of
# run.bend's result), written so that no list or text is matched while a
# second reference to it is alive: run.bend's insert shares every item it
# passes, same_run hands the buffer to take_ready and drop_ready at once, and
# flush keeps the item it writes as last while copying its text. Matching a
# value with two live references copies reference counts into all its fields.
# The machine keeps the last item written without its text (blank): the run
# only reads its key and its place (proof_fast_run.bend: the report is the
# same).

def blank(m: Maybe<&2, R.Item>) -> Maybe<&2, R.Item>:
  match m:
    case None{}:
      None{}
    case Some{R.Item{k, p, a, t}}:
      Some{R.Item{k, p, a, ""}}

def blank_st(st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, blank(l), b, k, o, ns, x}

# ---------------------------------------------------------------------------
# insert: the head's key is read when the head is matched, and passed on
# ---------------------------------------------------------------------------

# R.insert(e, x <> t); le: x's key is at most e's (ek).
def insert.go(t: List<&2, R.Item>, le: Bool, x: R.Item, e: R.Item, +ek: Nat) -> List<&2, R.Item>:
  match t le:
    case Nil{} True{}:
      x <> [e]
    case R.Item{+k, p, a, s} <> t2 True{}:
      x <> insert.go(t2, Nat.is_le(k, ek), R.Item{k, p, a, s}, e, ek)
    case t _:
      e <> x <> t

def insert.k(e: R.Item, +ek: Nat, buf: List<&2, R.Item>) -> List<&2, R.Item>:
  match buf:
    case Nil{}:
      [e]
    case R.Item{+k, p, a, s} <> t:
      insert.go(t, Nat.is_le(k, ek), R.Item{k, p, a, s}, e, ek)

def insert(e: R.Item, buf: List<&2, R.Item>) -> List<&2, R.Item>:
  match e:
    case R.Item{+k, p, a, s}:
      insert.k(R.Item{k, p, a, s}, k, buf)

# ---------------------------------------------------------------------------
# take_ready and drop_ready in one pass
# ---------------------------------------------------------------------------

type Two is Data:
  Two{take: List<&2, R.Item>, drop: List<&2, R.Item>}

def two.k(x: R.Item, t: Two) -> Two:
  match t:
    case Two{a, b}:
      Two{x <> a, b}

# Two{take_ready.go(x <> t, ok, ..), drop_ready.go(x <> t, ok, ..)}; ok: x is
# ready.
def ready.go(t: List<&2, R.Item>, ok: Bool, x: R.Item, +w: Nat, +inpos: Nat) -> Two:
  match t ok:
    case Nil{} True{}:
      Two{[x], Nil{}}
    case R.Item{+k, p, a, s} <> t2 True{}:
      two.k(x, ready.go(t2, Nat.is_le(Nat.add(k, w), inpos), R.Item{k, p, a, s}, w, inpos))
    case t _:
      Two{Nil{}, x <> t}

def ready(+w: Nat, +inpos: Nat, buf: List<&2, R.Item>) -> Two:
  match buf:
    case Nil{}:
      Two{Nil{}, Nil{}}
    case R.Item{+k, p, a, s} <> t:
      ready.go(t, Nat.is_le(Nat.add(k, w), inpos), R.Item{k, p, a, s}, w, inpos)

# ---------------------------------------------------------------------------
# flush: each text is moved into the output, last keeps no text
# ---------------------------------------------------------------------------

# R.flush(x <> t, ..) with its last blanked; ok: x is not below last.
def flush.go(t: List<&2, R.Item>, ok: Bool, x: R.Item, last: Maybe<&2, R.Item>) -> R.Flush:
  match t ok x:
    case Nil{} True{} R.Item{+k, +p, +a, s}:
      R.Flushed{s, Some{R.Item{k, p, a, ""}}}
    case R.Item{+k2, p2, a2, s2} <> t2 True{} R.Item{+k, +p, +a, s}:
      R.Flush.pre(s, flush.go(t2, Nat.is_le(k, k2), R.Item{k2, p2, a2, s2}, Some{R.Item{k, p, a, ""}}))
    case _ False{} R.Item{k, p, a, s}:
      R.Broke{"", a, R.at_of(last)}

def flush(items: List<&2, R.Item>, +last: Maybe<&2, R.Item>) -> R.Flush:
  match items:
    case Nil{}:
      R.Flushed{"", blank(last)}
    case R.Item{+k, p, a, s} <> t:
      flush.go(t, R.flush.ok(last, k), R.Item{k, p, a, s}, last)

# ---------------------------------------------------------------------------
# same_run, keyed, body_line over them
# ---------------------------------------------------------------------------

def same_run.k(t: Two, st: R.RunSt, l: Maybe<&2, R.Item>, +at: B.At) -> R.RunSt:
  match t:
    case Two{a, d}:
      R.emit.ready(flush(a, l), st, d, at)

def same_run(st: R.RunSt, +w: Nat, it: R.Item) -> R.RunSt:
  match st it:
    case R.RunSt{n, i, h, c, e, +l, b, k, o, ns, x} R.Item{+key, +inpos, +at, text}:
      same_run.k(ready(w, inpos, insert(R.Item{key, inpos, at, text}, b)), R.RunSt{n, i, h, c, e, blank(l), Nil{}, k, o, ns, x}, l, at)

def keyed.go(same: Bool, st2: R.RunSt, +w: Nat, +chrom: String, it: R.Item) -> R.RunSt:
  match same:
    case True{}:
      same_run(st2, w, it)
    case False{}:
      blank_st(R.new_run(st2, w, chrom, it))

def keyed(st: R.RunSt, +w: Nat, +it: R.Item, nts: List<&2, B.Note>, k2: R.Cnt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, +c, e, l, b, k, o, ns, x}:
      +chrom = R.Item.chrom(it)
      keyed.go(R.is_cur(c, chrom), R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, chrom, it)

def problem_line(strict: Bool, +st: R.RunSt, +w: Nat, +c: B.Code, +l: B.Line, +at: B.At, +inpos: Nat) -> R.RunSt:
  match strict:
    case True{}:
      blank_st(R.stop(st, "", B.Stop{c, Some{at}, None{}}))
    case False{}:
      keyed(st, w, R.Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))

def body_line(r: B.Res, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat) -> R.RunSt:
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      blank_st(R.stop(st, "", B.Stop{B.Malformed{}, Some{at}, None{}}))
    case B.Res{B.NoContig{}, k, t, s}:
      blank_st(R.stop(st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}}))
    case B.Res{B.Problem{+c}, k, t, s}:
      problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)
    case B.Res{B.Skipped{}, k, t, s}:
      keyed(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}))
    case B.Res{B.Normalized{}, k, +t, s}:
      keyed(st, R.Opts.w(o), R.Item{k, inpos, at, t ++ B.Line.term(l)}, R.stale_note(s, at), R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))
