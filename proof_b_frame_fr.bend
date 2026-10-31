import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_machine_nat.bend as PN

# Helpers for proof_b_frame.bend (adapted from proof_machine_frame.bend and
# proof_machine_sim.bend): run.bend's bookkeeping only ever appends to out
# and notes, so the spec goes on the same with what was collected before in
# front (pre); and a stopped run stays as it is.

# The same definition as proof_b_sim.bend's S.pre (proof_b_frame.bend
# bridges the two).
def pre(+O: String, +N: List<&2, B.Note>, rs: R.RunSt) -> R.RunSt:
  match rs:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, String.append(O, o), List.append(&2, B.Note, N, ns), x}

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

# -m: the records of a split line (L.pieces_in), a line that cannot be split
# (L.unsplit_in), and what B.Rec.parts says of a line (L.body_in).
law fr_piece:
  for +p: String
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +term: String
  for +at: B.At
  for +inpos: Nat
  {L.piece_in(R.RunSt.halt(pre(O, N, st)), p, fa, o, pre(O, N, st), term, at, inpos) == pre(O, N, L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)) : R.RunSt}

def fr_piece(p, fa, o, O, N, st, term, at, inpos):
  match st:
    case R.RunSt{+n, +i, +h, +cu, +e, +la, +b, +k, +so, +ns, +x}:
      match x:
        case True{}:
          {==}
        case False{}:
          fr_body_line(L.judge(fa, p), O, N, R.RunSt{n, i, h, cu, e, la, b, k, so, ns, False{}}, o, B.Line{p, term}, at, inpos)

law fr_pieces:
  for +ps: List<&2, String>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +term: String
  for +at: B.At
  for +inpos: Nat
  {L.pieces_in(ps, fa, o, pre(O, N, st), term, at, inpos) == pre(O, N, L.pieces_in(ps, fa, o, st, term, at, inpos)) : R.RunSt}

def fr_pieces(ps, fa, o, O, N, st, term, at, inpos):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +X = L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)
      %Equal.sym(R.RunSt, L.piece_in(R.RunSt.halt(pre(O, N, st)), p, fa, o, pre(O, N, st), term, at, inpos), pre(O, N, X), fr_piece(p, fa, o, O, N, st, term, at, inpos)) :
        {L.pieces_in(t, fa, o, _, term, at, inpos) == pre(O, N, L.pieces_in(t, fa, o, X, term, at, inpos)) : R.RunSt}
      fr_pieces(t, fa, o, O, N, X, term, at, inpos)

law fr_unsplit.k:
  for +b: Bool
  for +r: B.Res
  for +c: B.Code
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {Bool.pick(R.RunSt, b, R.body_line(r, pre(O, N, st), o, l, at, inpos), R.problem_line(R.Opts.strict(o), pre(O, N, st), R.Opts.w(o), c, l, at, inpos))
    == pre(O, N, Bool.pick(R.RunSt, b, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))) : R.RunSt}

def fr_unsplit.k(b, r, c, O, N, st, o, l, at, inpos):
  match b:
    case True{}:
      fr_body_line(r, O, N, st, o, l, at, inpos)
    case False{}:
      fr_problem_line(R.Opts.strict(o), O, N, st, R.Opts.w(o), c, l, at, inpos)

law fr_body_in:
  for +pt: B.Parts
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {L.body_in(pt, fa, o, pre(O, N, st), l, at, inpos) == pre(O, N, L.body_in(pt, fa, o, st, l, at, inpos)) : R.RunSt}

def fr_body_in(pt, fa, O, N, st, o, l, at, inpos):
  match pt:
    case B.Whole{}:
      fr_body_line(L.judge(fa, B.Line.body(l)), O, N, st, o, l, at, inpos)
    case B.Pieces{+ps}:
      fr_pieces(ps, fa, o, O, N, st, B.Line.term(l), at, inpos)
    case B.Unsplit{+c}:
      fr_unsplit.k(L.stops(L.judge(fa, B.Line.body(l)), R.Opts.strict(o)), L.judge(fa, B.Line.body(l)), c, O, N, st, o, l, at, inpos)

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

law ib_piece:
  for +p: String
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +term: String
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.inbody(L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)) == R.RunSt.inbody(st) : Bool}

def ib_piece(p, fa, o, st, term, at, inpos):
  match st:
    case R.RunSt{+n, +i, +h, +cu, +e, +la, +b, +k, +so, +ns, +x}:
      match x:
        case True{}:
          {==}
        case False{}:
          ib_body_line(L.judge(fa, p), R.RunSt{n, i, h, cu, e, la, b, k, so, ns, False{}}, o, B.Line{p, term}, at, inpos)

law ib_pieces:
  for +ps: List<&2, String>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +term: String
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.inbody(L.pieces_in(ps, fa, o, st, term, at, inpos)) == R.RunSt.inbody(st) : Bool}

def ib_pieces(ps, fa, o, st, term, at, inpos):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +X = L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)
      Equal.trans(Bool, R.RunSt.inbody(L.pieces_in(t, fa, o, X, term, at, inpos)), R.RunSt.inbody(X), R.RunSt.inbody(st),
        ib_pieces(t, fa, o, X, term, at, inpos), ib_piece(p, fa, o, st, term, at, inpos))

law ib_unsplit.k:
  for +b: Bool
  for +r: B.Res
  for +c: B.Code
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.inbody(Bool.pick(R.RunSt, b, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))) == R.RunSt.inbody(st) : Bool}

def ib_unsplit.k(b, r, c, st, o, l, at, inpos):
  match b:
    case True{}:
      ib_body_line(r, st, o, l, at, inpos)
    case False{}:
      ib_problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)

law ib_body_in:
  for +pt: B.Parts
  for +fa: List<&2, B.Contig>
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.inbody(L.body_in(pt, fa, o, st, l, at, inpos)) == R.RunSt.inbody(st) : Bool}

def ib_body_in(pt, fa, st, o, l, at, inpos):
  match pt:
    case B.Whole{}:
      ib_body_line(L.judge(fa, B.Line.body(l)), st, o, l, at, inpos)
    case B.Pieces{+ps}:
      ib_pieces(ps, fa, o, st, B.Line.term(l), at, inpos)
    case B.Unsplit{+c}:
      ib_unsplit.k(L.stops(L.judge(fa, B.Line.body(l)), R.Opts.strict(o)), L.judge(fa, B.Line.body(l)), c, st, o, l, at, inpos)

# One line, and the whole run
# ===========================

# Before the #CHROM line nothing has been written (O empty).
law head_pre:
  for +isc: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +he: {String.is_empty(O) && List.is_empty(&2, B.Note, N) == True{} : Bool}
  {R.head_line(isc, pre(O, N, st), o, l) == pre(O, N, R.head_line(isc, st, o, l)) : R.RunSt}

def head_pre(isc, O, N, st, o, l, he):
  match O:
    case SNil{}:
      fr_head_line(isc, N, st, o, l)
    case SCon{ch, t}:
      Empty.absurd({R.head_line(isc, pre(SCon{ch, t}, N, st), o, l) == pre(SCon{ch, t}, N, R.head_line(isc, st, o, l)) : R.RunSt},
        P.false_ne_true(he))

law step_pre:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +l: B.Line
  for +hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}
  {L.line_step(fa, dfs, o, pre(O, N, st), l) == pre(O, N, L.line_step(fa, dfs, o, st, l)) : R.RunSt}

def step_pre(dfs,fa, o, O, N, st, l, hg):
  match st:
    case R.RunSt{n, i, h, c, e, la, b, k, so, ns, True{}}:
      {==}
    case R.RunSt{n, False{}, h, c, e, la, b, k, so, ns, False{}}:
      head_pre(R.is_chrom_line(B.Line.body(l)), O, N, R.RunSt{1n+n, False{}, h, c, e, la, b, k, so, ns, False{}}, o, l, hg)
    case R.RunSt{n, True{}, h, c, e, la, b, k, so, ns, False{}}:
      +fs = B.Rec.fields(B.Line.body(l))
      fr_body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, O, N, R.RunSt{1n+n, True{}, h, c, e, la, b, k, so, ns, False{}}, o, l,
        B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

# A line read in the body leaves the run in the body.
law ib_step:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +hi: {R.RunSt.inbody(st) == True{} : Bool}
  {R.RunSt.inbody(L.line_step(fa, dfs, o, st, l)) == True{} : Bool}

def ib_step(dfs,fa, o, st, l, hi):
  match st:
    case R.RunSt{n, i, h, c, e, la, b, k, so, ns, True{}}:
      hi
    case R.RunSt{n, False{}, h, c, e, la, b, k, so, ns, False{}}:
      Empty.absurd({R.RunSt.inbody(L.line_step(fa, dfs, o, R.RunSt{n, False{}, h, c, e, la, b, k, so, ns, False{}}, l)) == True{} : Bool},
        P.false_ne_true(hi))
    case R.RunSt{n, True{}, h, c, e, la, b, k, so, ns, False{}}:
      +fs = B.Rec.fields(B.Line.body(l))
      ib_body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, R.RunSt{1n+n, True{}, h, c, e, la, b, k, so, ns, False{}}, o, l,
        B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

law or_true_r:
  for +a: Bool
  {Bool.or(a, True{}) == True{} : Bool}

def or_true_r(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law hg_go:
  for +dfs: B.Defs
  for +c: Bool
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +E: Bool
  for +st: R.RunSt
  for +l: B.Line
  for +hc: {R.RunSt.inbody(st) == c : Bool}
  for +hg: {Bool.or(c, E) == True{} : Bool}
  {Bool.or(R.RunSt.inbody(L.line_step(fa, dfs, o, st, l)), E) == True{} : Bool}

def hg_go(dfs,c, fa, o, E, st, l, hc, hg):
  match c:
    case True{}:
      %Equal.sym(Bool, R.RunSt.inbody(L.line_step(fa, dfs, o, st, l)), True{}, ib_step(dfs, fa, o, st, l, hc)) :
        {Bool.or(_, E) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, E, True{}, hg) : {Bool.or(R.RunSt.inbody(L.line_step(fa, dfs, o, st, l)), _) == True{} : Bool}
      or_true_r(R.RunSt.inbody(L.line_step(fa, dfs, o, st, l)))

# The guard of step_pre holds after a line.
law hg_step:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +l: B.Line
  for +hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}
  {R.RunSt.inbody(L.line_step(fa, dfs, o, st, l)) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}

def hg_step(dfs,fa, o, O, N, st, l, hg):
  hg_go(dfs, R.RunSt.inbody(st), fa, o, String.is_empty(O) && List.is_empty(&2, B.Note, N), st, l, {==}, hg)

law run_pre:
  for +dfs: B.Defs
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}
  {L.run.go(ls, fa, dfs, o, pre(O, N, st)) == pre(O, N, L.run.go(ls, fa, dfs, o, st)) : R.RunSt}

def run_pre(dfs,ls, fa, o, O, N, st, hg):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      %Equal.sym(R.RunSt, L.line_step(fa, dfs, o, pre(O, N, st), l), pre(O, N, L.line_step(fa, dfs, o, st, l)), step_pre(dfs, fa, o, O, N, st, l, hg)) :
        {L.run.go(t, fa, dfs, o, _) == pre(O, N, L.run.go(t, fa, dfs, o, L.line_step(fa, dfs, o, st, l))) : R.RunSt}
      run_pre(dfs, t, fa, o, O, N, L.line_step(fa, dfs, o, st, l), hg_step(dfs, fa, o, O, N, st, l, hg))

# The end of the run
# ==================

law rep_eq:
  for +o1: String
  for +o2: String
  for +n1: List<&2, B.Note>
  for +n2: List<&2, B.Note>
  for +c: Nat
  for eo: {o1 == o2 : String}
  for en: {n1 == n2 : List<&2, B.Note>}
  {R.Report{o1, n1, c} == R.Report{o2, n2, c} : R.Report}

def rep_eq(o1, o2, n1, n2, c, eo, en):
  %eo : {R.Report{o1, n1, c} == R.Report{_, n2, c} : R.Report}
  %en : {R.Report{o1, n1, c} == R.Report{o1, _, c} : R.Report}
  {==}

law ff_pre:
  for +f: R.Flush
  for +O: String
  for +N: List<&2, B.Note>
  for +o: String
  for +ns: List<&2, B.Note>
  for +k: R.Cnt
  {R.finish.flush(f, String.append(O, o), List.append(&2, B.Note, N, ns), k) == R.Report{String.append(O, R.Report.out(R.finish.flush(f, o, ns, k))), List.append(&2, B.Note, N, R.Report.notes(R.finish.flush(f, o, ns, k))), R.Report.code(R.finish.flush(f, o, ns, k))} : R.Report}

def ff_pre(f, O, N, o, ns, k):
  match f k:
    case R.Broke{o2, bad, prev} _:
      +nt = {B.Stop{B.Unsorted{}, Some{bad}, prev} : B.Note}
      rep_eq(String.append(String.append(O, o), o2), String.append(O, String.append(o, o2)),
        List.append(&2, B.Note, List.append(&2, B.Note, N, ns), [nt]), List.append(&2, B.Note, N, List.append(&2, B.Note, ns, [nt])), 1n,
        PN.str_assoc(O, o, o2), P.append_assoc(B.Note, N, ns, [nt]))
    case R.Flushed{o2, l2} R.Cnt{a, ch, sk, wa}:
      +nt = {B.Summary{a, ch, sk, wa} : B.Note}
      rep_eq(String.append(String.append(O, o), o2), String.append(O, String.append(o, o2)),
        List.append(&2, B.Note, List.append(&2, B.Note, N, ns), [nt]), List.append(&2, B.Note, N, List.append(&2, B.Note, ns, [nt])), 0n,
        PN.str_assoc(O, o, o2), P.append_assoc(B.Note, N, ns, [nt]))

law nh_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +he: {String.is_empty(O) && List.is_empty(&2, B.Note, N) == True{} : Bool}
  {R.Report{"", [B.Stop{B.NoHeader{}, None{}, None{}}], 1n} == R.Report{String.append(O, ""), List.append(&2, B.Note, N, [B.Stop{B.NoHeader{}, None{}, None{}}]), 1n} : R.Report}

def nh_pre(O, N, he):
  match O N:
    case SNil{} Nil{}:
      {==}
    case SNil{} Con{x, t}:
      Empty.absurd({R.Report{"", [B.Stop{B.NoHeader{}, None{}, None{}}], 1n} == R.Report{"", List.append(&2, B.Note, x <> t, [B.Stop{B.NoHeader{}, None{}, None{}}]), 1n} : R.Report},
        P.false_ne_true(he))
    case SCon{ch, t} _:
      Empty.absurd({R.Report{"", [B.Stop{B.NoHeader{}, None{}, None{}}], 1n} == R.Report{String.append(SCon{ch, t}, ""), List.append(&2, B.Note, N, [B.Stop{B.NoHeader{}, None{}, None{}}]), 1n} : R.Report},
        P.false_ne_true(he))

law finish_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  for +hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}
  {R.finish(pre(O, N, st)) == R.Report{String.append(O, R.Report.out(R.finish(st))), List.append(&2, B.Note, N, R.Report.notes(R.finish(st))), R.Report.code(R.finish(st))} : R.Report}

def finish_pre(O, N, st, hg):
  match st:
    case R.RunSt{n, i, h, c, e, la, b, k, so, ns, True{}}:
      {==}
    case R.RunSt{n, False{}, h, c, e, la, b, k, so, ns, False{}}:
      nh_pre(O, N, hg)
    case R.RunSt{n, True{}, h, c, e, la, b, k, so, ns, False{}}:
      ff_pre(R.flush(b, la), O, N, so, ns, k)

# A stopped run
# =============

law run_halted:
  for +dfs: B.Defs
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +hh: {R.RunSt.halt(st) == True{} : Bool}
  {L.run.go(ls, fa, dfs, o, st) == st : R.RunSt}

def run_halted(dfs,ls, fa, o, st, hh):
  match ls st:
    case Nil{} _:
      {==}
    case l <> t R.RunSt{n, i, h, c, e, la, b, k, so, sns, True{}}:
      run_halted(dfs, t, fa, o, R.RunSt{n, i, h, c, e, la, b, k, so, sns, True{}}, hh)
    case l <> t R.RunSt{n, i, h, c, e, la, b, k, so, sns, False{}}:
      Empty.absurd({L.run.go(l <> t, fa, dfs, o, R.RunSt{n, i, h, c, e, la, b, k, so, sns, False{}}) == R.RunSt{n, i, h, c, e, la, b, k, so, sns, False{}} : R.RunSt},
        P.false_ne_true(hh))

# The header's definitions (L.defs) and one line
# ==============================================

# Once in the body, the definitions are those read so far.
law defs_done:
  for +ls: List<&2, B.Line>
  for +d: B.Defs
  {L.defs.go(ls, True{}, d) == d : B.Defs}

def defs_done(ls, d):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      defs_done(t, d)

# A header line's step reads no definitions.
law step_head:
  for +fa: List<&2, B.Contig>
  for +D1: B.Defs
  for +D2: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +h: {R.RunSt.inbody(st) == False{} : Bool}
  {L.line_step(fa, D1, o, st, l) == L.line_step(fa, D2, o, st, l) : R.RunSt}

def step_head(fa, D1, D2, o, st, l, h):
  match st:
    case R.RunSt{+n, +i, +hh, +c, +e, +la, +b, +k, +so, +ns, +x}:
      match i x:
        case _ True{}:
          {==}
        case False{} False{}:
          {==}
        case True{} False{}:
          Empty.absurd({L.line_step(fa, D1, o, R.RunSt{n, True{}, hh, c, e, la, b, k, so, ns, False{}}, l) == L.line_step(fa, D2, o, R.RunSt{n, True{}, hh, c, e, la, b, k, so, ns, False{}}, l) : R.RunSt},
            P.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))

# The definitions run reads, for the rest of the file from st on, are those
# the machine read so far (dfs) for a line's step: in the body they are dfs,
# and a header line reads none.
law ls_defs:
  for +fa: List<&2, B.Contig>
  for +ls: List<&2, B.Line>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  {L.line_step(fa, L.defs.go(ls, R.RunSt.inbody(st), dfs), o, st, l) == L.line_step(fa, dfs, o, st, l) : R.RunSt}

def ls_defs.k(+i: Bool, +fa: List<&2, B.Contig>, +ls: List<&2, B.Line>, +dfs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line,
  +hi: {R.RunSt.inbody(st) == i : Bool}) ->
  {L.line_step(fa, L.defs.go(ls, i, dfs), o, st, l) == L.line_step(fa, dfs, o, st, l) : R.RunSt}:
  match i:
    case True{}:
      %Equal.sym(B.Defs, L.defs.go(ls, True{}, dfs), dfs, defs_done(ls, dfs)) : {L.line_step(fa, _, o, st, l) == L.line_step(fa, dfs, o, st, l) : R.RunSt}
      {==}
    case False{}:
      step_head(fa, L.defs.go(ls, False{}, dfs), dfs, o, st, l, hi)

def ls_defs(fa, ls, dfs, o, st, l):
  ls_defs.k(R.RunSt.inbody(st), fa, ls, dfs, o, st, l, {==})

# A step from a run that has not stopped: in the body after it exactly when
# in the body before it or the line is the #CHROM line.
law ib_line:
  for +fa: List<&2, B.Contig>
  for +D: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +hx: {R.RunSt.halt(st) == False{} : Bool}
  {R.RunSt.inbody(L.line_step(fa, D, o, st, l)) == Bool.or(R.RunSt.inbody(st), R.is_chrom_line(B.Line.body(l))) : Bool}

def ib_line.h(+isc: Bool, +n: Nat, +hh: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +so: String, +ns: List<&2, B.Note>, +o: B.Opts, +l: B.Line) ->
  {R.RunSt.inbody(R.head_line(isc, R.RunSt{n, False{}, hh, c, e, la, b, k, so, ns, False{}}, o, l)) == isc : Bool}:
  match isc l:
    case True{} B.Line{+bd, +term}:
      {==}
    case False{} _:
      {==}

def ib_line(fa, D, o, st, l, hx):
  match st:
    case R.RunSt{+n, +i, +hh, +c, +e, +la, +b, +k, +so, +ns, +x}:
      match i x:
        case _ True{}:
          Empty.absurd({R.RunSt.inbody(L.line_step(fa, D, o, R.RunSt{n, i, hh, c, e, la, b, k, so, ns, True{}}, l)) == Bool.or(i, R.is_chrom_line(B.Line.body(l))) : Bool},
            P.false_ne_true(Equal.sym(Bool, True{}, False{}, hx)))
        case False{} False{}:
          ib_line.h(R.is_chrom_line(B.Line.body(l)), 1n+n, hh, c, e, la, b, k, so, ns, o, l)
        case True{} False{}:
          +fs = B.Rec.fields(B.Line.body(l))
          ib_body_in(B.Rec.parts(D, o, B.Line.body(l)), fa, R.RunSt{1n+n, True{}, hh, c, e, la, b, k, so, ns, False{}}, o, l,
            B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

