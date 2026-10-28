import Base
import ./types.bend as B
import ./run.bend as R
import ./proof_base.bend as P

# run.bend's bookkeeping keeps inbody (copied from proof_machine_frame.bend,
# whose import of norm.bend no longer checks; the lemmas are about run.bend
# only). A body line leaves inbody as it was.

# The bookkeeping keeps inbody
# ============================

law ib_stop:
  for +st: R.RunSt
  for +out: String
  for +nt: B.Note
  {R.RunSt.inbody(R.stop(st, out, nt)) == R.RunSt.inbody(st) : Bool}

def ib_stop(st, out, nt):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

law ib_emit:
  for +f: R.Flush
  for +st: R.RunSt
  for +rest: List<&2, R.Item>
  for +at: B.At
  {R.RunSt.inbody(R.emit.ready(f, st, rest, at)) == R.RunSt.inbody(st) : Bool}

def ib_emit(f, st, rest, at):
  match f st:
    case R.Broke{o2, bad, prev} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ib_stop(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{o2, l2} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

law ib_same_run:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  {R.RunSt.inbody(R.same_run(st, w, it)) == R.RunSt.inbody(st) : Bool}

def ib_same_run(st, w, it):
  match st it:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} R.Item{key, inpos, at, text}:
      +buf = R.insert(R.Item{key, inpos, at, text}, b)
      ib_emit(R.flush(R.take_ready(w, inpos, buf), l), R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x}, R.drop_ready(w, inpos, buf), at)

law ib_new_run_go:
  for +f: R.Flush
  for +again: Bool
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.RunSt.inbody(R.new_run.go(f, again, st, w, chrom, it)) == R.RunSt.inbody(st) : Bool}

def ib_new_run_go(f, again, st, w, chrom, it):
  match f again st:
    case R.Broke{o2, bad, prev} _ R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ib_stop(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{o2, l2} True{} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ib_stop(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}})
    case R.Flushed{o2, l2} False{} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ib_same_run(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), ns, x}, w, it)

law ib_new_run:
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.RunSt.inbody(R.new_run(st, w, chrom, it)) == R.RunSt.inbody(st) : Bool}

def ib_new_run(st, w, chrom, it):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ib_new_run_go(R.flush(b, l), R.has(chrom, e), R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)

law ib_keyed_go:
  for +same: Bool
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.RunSt.inbody(R.keyed.go(same, st, w, chrom, it)) == R.RunSt.inbody(st) : Bool}

def ib_keyed_go(same, st, w, chrom, it):
  match same:
    case True{}:
      ib_same_run(st, w, it)
    case False{}:
      ib_new_run(st, w, chrom, it)

law ib_keyed:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  for +nts: List<&2, B.Note>
  for +k2: R.Cnt
  {R.RunSt.inbody(R.keyed(st, w, it, nts, k2)) == R.RunSt.inbody(st) : Bool}

def ib_keyed(st, w, it, nts, k2):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ib_keyed_go(R.is_cur(c, R.Item.chrom(it)), R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, R.Item.chrom(it), it)

law ib_problem_line:
  for +strict: Bool
  for +st: R.RunSt
  for +w: Nat
  for +c: B.Code
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.inbody(R.problem_line(strict, st, w, c, l, at, inpos)) == R.RunSt.inbody(st) : Bool}

def ib_problem_line(strict, st, w, c, l, at, inpos):
  match strict st:
    case True{} _:
      ib_stop(st, "", B.Stop{c, Some{at}, None{}})
    case False{} R.RunSt{n, i, h, cu, e, la, b, k, o, ns, x}:
      ib_keyed(R.RunSt{n, i, h, cu, e, la, b, k, o, ns, x}, w, R.Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}],
        R.bump(k, False{}, False{}, True{}))

law ib_body_line:
  for +r: B.Res
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.inbody(R.body_line(r, st, o, l, at, inpos)) == R.RunSt.inbody(st) : Bool}

def ib_body_line(r, st, o, l, at, inpos):
  match r st:
    case B.Res{B.Broken{}, k, t, s} _:
      ib_stop(st, "", B.Stop{B.Malformed{}, Some{at}, None{}})
    case B.Res{B.NoContig{}, k, t, s} _:
      ib_stop(st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}})
    case B.Res{B.Problem{c}, k, t, s} _:
      ib_problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)
    case B.Res{B.Skipped{}, k, t, s} R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}:
      ib_keyed(R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, Nil{},
        R.bump(kk, False{}, True{}, False{}))
    case B.Res{B.Normalized{}, k, t, s} R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}:
      ib_keyed(R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}, R.Opts.w(o), R.Item{k, inpos, at, String.append(t, B.Line.term(l))},
        R.stale_note(s, at), R.bump(kk, Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))

