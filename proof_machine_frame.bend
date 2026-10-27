import Base
import ./types.bend as B
import ./run.bend as R
import ./norm.bend as Norm
import ./proof_base.bend as P
import ./proof_machine_nat.bend as PN

# Lemmas for the machine proof: the run's bookkeeping (run.bend) only ever
# appends to out and notes, so a state whose out and notes were handed on
# (Norm.RunSt.clear) goes on exactly as the full state, with the bytes and
# messages written before in front (pre).

def pre(+O: String, +N: List<&2, B.Note>, rs: R.RunSt) -> R.RunSt:
  match rs:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, String.append(O, o), List.append(&2, B.Note, N, ns), x}

# Before the #CHROM line, nothing is written yet.
def good(st: R.RunSt) -> Bool:
  match st:
    case R.RunSt{n, True{}, h, c, e, l, b, k, o, ns, x}:
      True{}
    case R.RunSt{n, False{}, h, c, e, l, b, k, SNil{}, Nil{}, x}:
      True{}
    case _:
      False{}

law rs_eq:
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o1: String
  for +o2: String
  for +n1: List<&2, B.Note>
  for +n2: List<&2, B.Note>
  for +x: Bool
  for eo: {o1 == o2 : String}
  for en: {n1 == n2 : List<&2, B.Note>}
  {R.RunSt{n, i, h, c, e, l, b, k, o1, n1, x} == R.RunSt{n, i, h, c, e, l, b, k, o2, n2, x} : R.RunSt}

def rs_eq(n, i, h, c, e, l, b, k, o1, o2, n1, n2, x, eo, en):
  %eo : {R.RunSt{n, i, h, c, e, l, b, k, o1, n1, x} == R.RunSt{n, i, h, c, e, l, b, k, _, n2, x} : R.RunSt}
  %en : {R.RunSt{n, i, h, c, e, l, b, k, o1, n1, x} == R.RunSt{n, i, h, c, e, l, b, k, o1, _, x} : R.RunSt}
  {==}

# Projections
# ===========

law out_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  {Norm.RunSt.out(pre(O, N, st)) == String.append(O, Norm.RunSt.out(st)) : String}

def out_pre(O, N, st):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

law notes_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  {Norm.RunSt.notes(pre(O, N, st)) == List.append(&2, B.Note, N, Norm.RunSt.notes(st)) : List<&2, B.Note>}

def notes_pre(O, N, st):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

law clear_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  {Norm.RunSt.clear(pre(O, N, st)) == Norm.RunSt.clear(st) : R.RunSt}

def clear_pre(O, N, st):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

# Every state is its cleared state with its out and notes in front.
law split_st:
  for +st: R.RunSt
  {st == pre(Norm.RunSt.out(st), Norm.RunSt.notes(st), Norm.RunSt.clear(st)) : R.RunSt}

def split_st(st):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      rs_eq(n, i, h, c, e, l, b, k, o, String.append(o, ""), ns, List.append(&2, B.Note, ns, Nil{}), x,
        Equal.sym(String, String.append(o, ""), o, PN.str_nil(o)),
        Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, ns, Nil{}), ns, P.append_nil(B.Note, ns)))

law good_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +hi: {R.RunSt.inbody(st) == True{} : Bool}
  {good(pre(O, N, st)) == True{} : Bool}

def good_pre(O, N, st, hi):
  match st:
    case R.RunSt{n, True{}, h, c, e, l, b, k, o, ns, x}:
      {==}
    case R.RunSt{n, False{}, h, c, e, l, b, k, o, ns, x}:
      Empty.absurd({good(pre(O, N, R.RunSt{n, False{}, h, c, e, l, b, k, o, ns, x})) == True{} : Bool}, P.false_ne_true(hi))

# Frame: the bookkeeping commutes with pre
# ========================================

law fr_tick:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  {R.tick(pre(O, N, st)) == pre(O, N, R.tick(st)) : R.RunSt}

def fr_tick(O, N, st):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

law fr_stop:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +out: String
  for +nt: B.Note
  {R.stop(pre(O, N, st), out, nt) == pre(O, N, R.stop(st, out, nt)) : R.RunSt}

def fr_stop(O, N, st, out, nt):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      rs_eq(n, i, h, c, e, l, b, k, String.append(String.append(O, o), out), String.append(O, String.append(o, out)),
        List.append(&2, B.Note, List.append(&2, B.Note, N, ns), [nt]), List.append(&2, B.Note, N, List.append(&2, B.Note, ns, [nt])), True{},
        PN.str_assoc(O, o, out), P.append_assoc(B.Note, N, ns, [nt]))

law fr_emit:
  for +f: R.Flush
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +rest: List<&2, R.Item>
  for +at: B.At
  {R.emit.ready(f, pre(O, N, st), rest, at) == pre(O, N, R.emit.ready(f, st, rest, at)) : R.RunSt}

def fr_emit(f, O, N, st, rest, at):
  match f st:
    case R.Broke{o2, bad, prev} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      fr_stop(O, N, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{o2, l2} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      rs_eq(n, i, h, c, e, l2, rest, k, String.append(String.append(O, o), o2), String.append(O, String.append(o, o2)),
        List.append(&2, B.Note, N, ns), List.append(&2, B.Note, N, ns), x,
        PN.str_assoc(O, o, o2), {==})

law fr_same_run:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  {R.same_run(pre(O, N, st), w, it) == pre(O, N, R.same_run(st, w, it)) : R.RunSt}

def fr_same_run(O, N, st, w, it):
  match st it:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} R.Item{key, inpos, at, text}:
      +buf = R.insert(R.Item{key, inpos, at, text}, b)
      fr_emit(R.flush(R.take_ready(w, inpos, buf), l), O, N, R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x},
        R.drop_ready(w, inpos, buf), at)

law fr_new_run_go:
  for +f: R.Flush
  for +again: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.new_run.go(f, again, pre(O, N, st), w, chrom, it) == pre(O, N, R.new_run.go(f, again, st, w, chrom, it)) : R.RunSt}

def fr_new_run_go(f, again, O, N, st, w, chrom, it):
  match f again st:
    case R.Broke{o2, bad, prev} _ R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      fr_stop(O, N, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{o2, l2} True{} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      fr_stop(O, N, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}})
    case R.Flushed{o2, l2} False{} R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      %Equal.sym(String, String.append(String.append(O, o), o2), String.append(O, String.append(o, o2)), PN.str_assoc(O, o, o2)) :
        {R.same_run(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, _, List.append(&2, B.Note, N, ns), x}, w, it)
          == pre(O, N, R.same_run(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), ns, x}, w, it)) : R.RunSt}
      fr_same_run(O, N, R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), ns, x}, w, it)

law fr_new_run:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.new_run(pre(O, N, st), w, chrom, it) == pre(O, N, R.new_run(st, w, chrom, it)) : R.RunSt}

def fr_new_run(O, N, st, w, chrom, it):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      fr_new_run_go(R.flush(b, l), R.has(chrom, e), O, N, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)

law fr_keyed_go:
  for +same: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.keyed.go(same, pre(O, N, st), w, chrom, it) == pre(O, N, R.keyed.go(same, st, w, chrom, it)) : R.RunSt}

def fr_keyed_go(same, O, N, st, w, chrom, it):
  match same:
    case True{}:
      fr_same_run(O, N, st, w, it)
    case False{}:
      fr_new_run(O, N, st, w, chrom, it)

law fr_keyed:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  for +nts: List<&2, B.Note>
  for +k2: R.Cnt
  {R.keyed(pre(O, N, st), w, it, nts, k2) == pre(O, N, R.keyed(st, w, it, nts, k2)) : R.RunSt}

def fr_keyed(O, N, st, w, it, nts, k2):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), nts),
        List.append(&2, B.Note, N, List.append(&2, B.Note, ns, nts)), P.append_assoc(B.Note, N, ns, nts)) :
        {R.keyed.go(R.is_cur(c, R.Item.chrom(it)), R.RunSt{n, i, h, c, e, l, b, k2, String.append(O, o), _, x}, w, R.Item.chrom(it), it)
          == pre(O, N, R.keyed.go(R.is_cur(c, R.Item.chrom(it)), R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, R.Item.chrom(it), it)) : R.RunSt}
      fr_keyed_go(R.is_cur(c, R.Item.chrom(it)), O, N, R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, R.Item.chrom(it), it)

law fr_problem_line:
  for +strict: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +w: Nat
  for +c: B.Code
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.problem_line(strict, pre(O, N, st), w, c, l, at, inpos) == pre(O, N, R.problem_line(strict, st, w, c, l, at, inpos)) : R.RunSt}

def fr_problem_line(strict, O, N, st, w, c, l, at, inpos):
  match strict st:
    case True{} _:
      fr_stop(O, N, st, "", B.Stop{c, Some{at}, None{}})
    case False{} R.RunSt{n, i, h, cu, e, la, b, k, o, ns, x}:
      fr_keyed(O, N, R.RunSt{n, i, h, cu, e, la, b, k, o, ns, x}, w, R.Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}],
        R.bump(k, False{}, False{}, True{}))

law fr_body_line:
  for +r: B.Res
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.body_line(r, pre(O, N, st), o, l, at, inpos) == pre(O, N, R.body_line(r, st, o, l, at, inpos)) : R.RunSt}

def fr_body_line(r, O, N, st, o, l, at, inpos):
  match r st:
    case B.Res{B.Broken{}, k, t, s} _:
      fr_stop(O, N, st, "", B.Stop{B.Malformed{}, Some{at}, None{}})
    case B.Res{B.NoContig{}, k, t, s} _:
      fr_stop(O, N, st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}})
    case B.Res{B.Problem{c}, k, t, s} _:
      fr_problem_line(R.Opts.strict(o), O, N, st, R.Opts.w(o), c, l, at, inpos)
    case B.Res{B.Skipped{}, k, t, s} R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}:
      fr_keyed(O, N, R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, Nil{},
        R.bump(kk, False{}, True{}, False{}))
    case B.Res{B.Normalized{}, k, t, s} R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}:
      fr_keyed(O, N, R.RunSt{n, i, h, cu, e, la, b, kk, so, ns, x}, R.Opts.w(o), R.Item{k, inpos, at, String.append(t, B.Line.term(l))},
        R.stale_note(s, at), R.bump(kk, Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))

# Before the #CHROM line nothing was written, so a header line is the same.
law fr_head_line:
  for +isc: Bool
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  {R.head_line(isc, pre("", N, st), o, l) == pre("", N, R.head_line(isc, st, o, l)) : R.RunSt}

def fr_head_line(isc, N, st, o, l):
  match isc st l:
    case True{} R.RunSt{n, i, h, c, e, la, b, k, out, ns, x} B.Line{bd, term}:
      {==}
    case False{} R.RunSt{n, i, h, c, e, la, b, k, out, ns, x} _:
      {==}

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
