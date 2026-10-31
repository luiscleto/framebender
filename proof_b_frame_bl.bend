import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_b_defs.bend as PD
import ./proof_base.bend as P

# Helpers for proof_b_frame.bend: a run's report does not depend on the text
# of the last item written (PD.blank_st). Adapted from proof_fast_run.bend,
# whose route went through the old String machine's bookkeeping; here every
# lemma is about run.bend's functions directly, up to blank_st.

# A flush result with its last item's text blanked.
def bF(f: R.Flush) -> R.Flush:
  match f:
    case R.Flushed{o, l}:
      R.Flushed{o, PD.blank(l)}
    case R.Broke{o, b, p}:
      R.Broke{o, b, p}

law blank_blank:
  for +L: Maybe<&2, R.Item>
  {PD.blank(PD.blank(L)) == PD.blank(L) : Maybe<&2, R.Item>}

def blank_blank(L):
  match L:
    case None{}:
      {==}
    case Some{R.Item{+k, +p, +a, +t}}:
      {==}

law ok_blank:
  for +L: Maybe<&2, R.Item>
  for +k: Nat
  {R.flush.ok(PD.blank(L), k) == R.flush.ok(L, k) : Bool}

def ok_blank(L, k):
  match L:
    case None{}:
      {==}
    case Some{R.Item{+lk, +p, +a, +t}}:
      {==}

law at_blank:
  for +L: Maybe<&2, R.Item>
  {R.at_of(PD.blank(L)) == R.at_of(L) : Maybe<&2, B.At>}

def at_blank(L):
  match L:
    case None{}:
      {==}
    case Some{R.Item{+lk, +p, +a, +t}}:
      {==}

# flush
# =====

law put_bl:
  for +ok: Bool
  for +x: R.Item
  for +L: Maybe<&2, R.Item>
  for +rest: R.Flush
  {R.flush.put(ok, x, PD.blank(L), rest) == R.flush.put(ok, x, L, rest) : R.Flush}

def put_bl(ok, x, L, rest):
  match ok:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, B.At>, R.at_of(PD.blank(L)), R.at_of(L), at_blank(L)) :
        {R.Broke{"", R.Item.at(x), _} == R.Broke{"", R.Item.at(x), R.at_of(L)} : R.Flush}
      {==}

# flush's result, up to its last item's text, does not read last's text.
law flush_bl:
  for +items: List<&2, R.Item>
  for +L: Maybe<&2, R.Item>
  {bF(R.flush(items, PD.blank(L))) == bF(R.flush(items, L)) : R.Flush}

def flush_bl(items, L):
  match items:
    case Nil{}:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(L)), PD.blank(L), blank_blank(L)) :
        {R.Flushed{"", _} == R.Flushed{"", PD.blank(L)} : R.Flush}
      {==}
    case +x <> +t:
      %Equal.sym(Bool, R.flush.ok(PD.blank(L), R.Item.key(x)), R.flush.ok(L, R.Item.key(x)), ok_blank(L, R.Item.key(x))) :
        {bF(R.flush.put(_, x, PD.blank(L), R.flush(t, Some{x}))) == bF(R.flush.put(R.flush.ok(L, R.Item.key(x)), x, L, R.flush(t, Some{x}))) : R.Flush}
      %Equal.sym(R.Flush, R.flush.put(R.flush.ok(L, R.Item.key(x)), x, PD.blank(L), R.flush(t, Some{x})),
        R.flush.put(R.flush.ok(L, R.Item.key(x)), x, L, R.flush(t, Some{x})),
        put_bl(R.flush.ok(L, R.Item.key(x)), x, L, R.flush(t, Some{x}))) :
        {bF(_) == bF(R.flush.put(R.flush.ok(L, R.Item.key(x)), x, L, R.flush(t, Some{x}))) : R.Flush}
      {==}

# stop, emit.ready, same_run
# ==========================

law stop_bl:
  for +st: R.RunSt
  for +out: String
  for +nt: B.Note
  {PD.blank_st(R.stop(PD.blank_st(st), out, nt)) == PD.blank_st(R.stop(st, out, nt)) : R.RunSt}

def stop_bl(st, out, nt):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(l)), PD.blank(l), blank_blank(l)) :
        {R.RunSt{n, i, h, c, e, _, b, k, String.append(o, out), List.append(&2, B.Note, ns, [nt]), True{}} == PD.blank_st(R.stop(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, out, nt)) : R.RunSt}
      {==}

law emit_bF:
  for +f: R.Flush
  for +st: R.RunSt
  for +d: List<&2, R.Item>
  for +at: B.At
  {PD.blank_st(R.emit.ready(bF(f), st, d, at)) == PD.blank_st(R.emit.ready(f, st, d, at)) : R.RunSt}

def emit_bF(f, st, d, at):
  match f st:
    case R.Flushed{+o2, +l2} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(l2)), PD.blank(l2), blank_blank(l2)) :
        {R.RunSt{n, i, h, c, e, _, d, k, String.append(o, o2), ns, x} == R.RunSt{n, i, h, c, e, PD.blank(l2), d, k, String.append(o, o2), ns, x} : R.RunSt}
      {==}
    case R.Broke{+o2, +bad, +prev} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law emit_st:
  for +f: R.Flush
  for +st: R.RunSt
  for +d: List<&2, R.Item>
  for +at: B.At
  {PD.blank_st(R.emit.ready(f, PD.blank_st(st), d, at)) == PD.blank_st(R.emit.ready(f, st, d, at)) : R.RunSt}

def emit_st(f, st, d, at):
  match f st:
    case R.Flushed{+o2, +l2} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}
    case R.Broke{+o2, +bad, +prev} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      stop_bl(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{bad}, prev})

# Writing items after last, then going on: last's text is not read.
law emit_both:
  for +L: Maybe<&2, R.Item>
  for +items: List<&2, R.Item>
  for +st: R.RunSt
  for +d: List<&2, R.Item>
  for +at: B.At
  {PD.blank_st(R.emit.ready(R.flush(items, PD.blank(L)), PD.blank_st(st), d, at)) == PD.blank_st(R.emit.ready(R.flush(items, L), st, d, at)) : R.RunSt}

def emit_both(L, items, st, d, at):
  +F1 = R.flush(items, PD.blank(L))
  +F2 = R.flush(items, L)
  +bs = PD.blank_st(st)
  Equal.trans(R.RunSt, PD.blank_st(R.emit.ready(F1, bs, d, at)), PD.blank_st(R.emit.ready(bF(F1), bs, d, at)), PD.blank_st(R.emit.ready(F2, st, d, at)),
    Equal.sym(R.RunSt, PD.blank_st(R.emit.ready(bF(F1), bs, d, at)), PD.blank_st(R.emit.ready(F1, bs, d, at)), emit_bF(F1, bs, d, at)),
    Equal.trans(R.RunSt, PD.blank_st(R.emit.ready(bF(F1), bs, d, at)), PD.blank_st(R.emit.ready(bF(F2), bs, d, at)), PD.blank_st(R.emit.ready(F2, st, d, at)),
      Equal.cong(R.Flush, R.RunSt, z => PD.blank_st(R.emit.ready(z, bs, d, at)), bF(F1), bF(F2), flush_bl(items, L)),
      Equal.trans(R.RunSt, PD.blank_st(R.emit.ready(bF(F2), bs, d, at)), PD.blank_st(R.emit.ready(F2, bs, d, at)), PD.blank_st(R.emit.ready(F2, st, d, at)),
        emit_bF(F2, bs, d, at), emit_st(F2, st, d, at))))

law same_run_bl:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  {PD.blank_st(R.same_run(PD.blank_st(st), w, it)) == PD.blank_st(R.same_run(st, w, it)) : R.RunSt}

def same_run_bl(st, w, it):
  match st it:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x} R.Item{+key, +inpos, +at, +text}:
      +buf = R.insert(R.Item{key, inpos, at, text}, b)
      emit_both(l, R.take_ready(w, inpos, buf), R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x}, R.drop_ready(w, inpos, buf), at)

# new_run
# =======

law ng_bF:
  for +f: R.Flush
  for +g: Bool
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.new_run.go(bF(f), g, st, w, chrom, it) == R.new_run.go(f, g, st, w, chrom, it) : R.RunSt}

def ng_bF(f, g, st, w, chrom, it):
  match f g st:
    case R.Broke{+o, +bad, +prev} _ R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      {==}
    case R.Flushed{+o2, +l2} True{} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      {==}
    case R.Flushed{+o2, +l2} False{} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      {==}

law ng_st:
  for +f: R.Flush
  for +g: Bool
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {PD.blank_st(R.new_run.go(f, g, PD.blank_st(st), w, chrom, it)) == PD.blank_st(R.new_run.go(f, g, st, w, chrom, it)) : R.RunSt}

def ng_st(f, g, st, w, chrom, it):
  match f g st:
    case R.Broke{+o, +bad, +prev} _ R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      stop_bl(R.RunSt{n, i, h, c, e, l, b, k, so, ns, x}, o, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{+o2, +l2} True{} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      stop_bl(R.RunSt{n, i, h, c, e, l, b, k, so, ns, x}, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}})
    case R.Flushed{+o2, +l2} False{} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      {==}

law new_run_bl:
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {PD.blank_st(R.new_run(PD.blank_st(st), w, chrom, it)) == PD.blank_st(R.new_run(st, w, chrom, it)) : R.RunSt}

def new_run_bl(st, w, chrom, it):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +g = R.has(chrom, e)
      +S0 = {R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} : R.RunSt}
      +bs = PD.blank_st(S0)
      +F1 = R.flush(b, PD.blank(l))
      +F2 = R.flush(b, l)
      Equal.trans(R.RunSt, PD.blank_st(R.new_run.go(F1, g, bs, w, chrom, it)), PD.blank_st(R.new_run.go(F2, g, bs, w, chrom, it)), PD.blank_st(R.new_run.go(F2, g, S0, w, chrom, it)),
        Equal.cong(R.RunSt, R.RunSt, z => PD.blank_st(z), R.new_run.go(F1, g, bs, w, chrom, it), R.new_run.go(F2, g, bs, w, chrom, it),
          Equal.trans(R.RunSt, R.new_run.go(F1, g, bs, w, chrom, it), R.new_run.go(bF(F1), g, bs, w, chrom, it), R.new_run.go(F2, g, bs, w, chrom, it),
            Equal.sym(R.RunSt, R.new_run.go(bF(F1), g, bs, w, chrom, it), R.new_run.go(F1, g, bs, w, chrom, it), ng_bF(F1, g, bs, w, chrom, it)),
            Equal.trans(R.RunSt, R.new_run.go(bF(F1), g, bs, w, chrom, it), R.new_run.go(bF(F2), g, bs, w, chrom, it), R.new_run.go(F2, g, bs, w, chrom, it),
              Equal.cong(R.Flush, R.RunSt, z => R.new_run.go(z, g, bs, w, chrom, it), bF(F1), bF(F2), flush_bl(b, l)),
              ng_bF(F2, g, bs, w, chrom, it)))),
        ng_st(F2, g, S0, w, chrom, it))

# keyed, problem_line, body_line, head_line
# =========================================

law keyed_go_bl:
  for +same: Bool
  for +st2: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {PD.blank_st(R.keyed.go(same, PD.blank_st(st2), w, chrom, it)) == PD.blank_st(R.keyed.go(same, st2, w, chrom, it)) : R.RunSt}

def keyed_go_bl(same, st2, w, chrom, it):
  match same:
    case True{}:
      same_run_bl(st2, w, it)
    case False{}:
      new_run_bl(st2, w, chrom, it)

law keyed_bl:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  for +nts: List<&2, B.Note>
  for +k2: R.Cnt
  {PD.blank_st(R.keyed(PD.blank_st(st), w, it, nts, k2)) == PD.blank_st(R.keyed(st, w, it, nts, k2)) : R.RunSt}

def keyed_bl(st, w, it, nts, k2):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +chrom = R.Item.chrom(it)
      keyed_go_bl(R.is_cur(c, chrom), R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, chrom, it)

law problem_bl:
  for +strict: Bool
  for +st: R.RunSt
  for +w: Nat
  for +c: B.Code
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {PD.blank_st(R.problem_line(strict, PD.blank_st(st), w, c, l, at, inpos)) == PD.blank_st(R.problem_line(strict, st, w, c, l, at, inpos)) : R.RunSt}

def problem_bl(strict, st, w, c, l, at, inpos):
  match strict st:
    case True{} _:
      stop_bl(st, "", B.Stop{c, Some{at}, None{}})
    case False{} R.RunSt{+n, +i, +h, +cc, +e, +la, +b, +k, +so, +ns, +x}:
      keyed_bl(R.RunSt{n, i, h, cc, e, la, b, k, so, ns, x}, w, R.Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}], R.bump(k, False{}, False{}, True{}))

law body_line_bl:
  for +r: B.Res
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {PD.blank_st(R.body_line(r, PD.blank_st(st), o, l, at, inpos)) == PD.blank_st(R.body_line(r, st, o, l, at, inpos)) : R.RunSt}

def body_line_bl(r, st, o, l, at, inpos):
  match r st:
    case B.Res{B.Broken{}, +kk, +t, +s} _:
      stop_bl(st, "", B.Stop{B.Malformed{}, Some{at}, None{}})
    case B.Res{B.NoContig{}, +kk, +t, +s} _:
      stop_bl(st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}})
    case B.Res{B.Problem{+c2}, +kk, +t, +s} _:
      problem_bl(R.Opts.strict(o), st, R.Opts.w(o), c2, l, at, inpos)
    case B.Res{B.Skipped{}, +kk, +t, +s} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      keyed_bl(R.RunSt{n, i, h, c, e, la, b, k, so, ns, x}, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, Nil{}, R.bump(k, False{}, True{}, False{}))
    case B.Res{B.Normalized{}, +kk, +t, +s} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      keyed_bl(R.RunSt{n, i, h, c, e, la, b, k, so, ns, x}, R.Opts.w(o), R.Item{kk, inpos, at, t ++ B.Line.term(l)}, R.stale_note(s, at),
        R.bump(k, Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))

law blank_st2:
  for +st: R.RunSt
  {PD.blank_st(PD.blank_st(st)) == PD.blank_st(st) : R.RunSt}

def blank_st2(st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), blank_blank(la)) :
        {R.RunSt{n, i, h, c, e, _, b, k, so, ns, x} == R.RunSt{n, i, h, c, e, PD.blank(la), b, k, so, ns, x} : R.RunSt}
      {==}

# -m: the records of a split line, a line that cannot be split, and what
# B.Rec.parts says of a line.
law piece_bl:
  for +p: String
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +term: String
  for +at: B.At
  for +inpos: Nat
  {PD.blank_st(L.piece_in(R.RunSt.halt(PD.blank_st(st)), p, fa, o, PD.blank_st(st), term, at, inpos)) == PD.blank_st(L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)) : R.RunSt}

def piece_bl(p, fa, o, st, term, at, inpos):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      match x:
        case True{}:
          %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), blank_blank(la)) :
            {R.RunSt{n, i, h, c, e, _, b, k, so, ns, True{}} == R.RunSt{n, i, h, c, e, PD.blank(la), b, k, so, ns, True{}} : R.RunSt}
          {==}
        case False{}:
          body_line_bl(L.judge(fa, p), R.RunSt{n, i, h, c, e, la, b, k, so, ns, False{}}, o, B.Line{p, term}, at, inpos)

law pieces_bl:
  for +ps: List<&2, String>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +term: String
  for +at: B.At
  for +inpos: Nat
  {PD.blank_st(L.pieces_in(ps, fa, o, PD.blank_st(st), term, at, inpos)) == PD.blank_st(L.pieces_in(ps, fa, o, st, term, at, inpos)) : R.RunSt}

def pieces_bl(ps, fa, o, st, term, at, inpos):
  match ps:
    case Nil{}:
      blank_st2(st)
    case Con{+p, +t}:
      +X1 = L.piece_in(R.RunSt.halt(PD.blank_st(st)), p, fa, o, PD.blank_st(st), term, at, inpos)
      +X2 = L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)
      +E1 = piece_bl(p, fa, o, st, term, at, inpos)
      Equal.trans(R.RunSt, PD.blank_st(L.pieces_in(t, fa, o, X1, term, at, inpos)), PD.blank_st(L.pieces_in(t, fa, o, PD.blank_st(X1), term, at, inpos)), PD.blank_st(L.pieces_in(t, fa, o, X2, term, at, inpos)),
        Equal.sym(R.RunSt, PD.blank_st(L.pieces_in(t, fa, o, PD.blank_st(X1), term, at, inpos)), PD.blank_st(L.pieces_in(t, fa, o, X1, term, at, inpos)), pieces_bl(t, fa, o, X1, term, at, inpos)),
        {%Equal.sym(R.RunSt, PD.blank_st(X1), PD.blank_st(X2), E1) : {PD.blank_st(L.pieces_in(t, fa, o, _, term, at, inpos)) == PD.blank_st(L.pieces_in(t, fa, o, X2, term, at, inpos)) : R.RunSt};
          pieces_bl(t, fa, o, X2, term, at, inpos) : {PD.blank_st(L.pieces_in(t, fa, o, PD.blank_st(X1), term, at, inpos)) == PD.blank_st(L.pieces_in(t, fa, o, X2, term, at, inpos)) : R.RunSt}})

law unsplit_bl.k:
  for +b: Bool
  for +r: B.Res
  for +c: B.Code
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {PD.blank_st(Bool.pick(R.RunSt, b, R.body_line(r, PD.blank_st(st), o, l, at, inpos), R.problem_line(R.Opts.strict(o), PD.blank_st(st), R.Opts.w(o), c, l, at, inpos)))
    == PD.blank_st(Bool.pick(R.RunSt, b, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))) : R.RunSt}

def unsplit_bl.k(b, r, c, st, o, l, at, inpos):
  match b:
    case True{}:
      body_line_bl(r, st, o, l, at, inpos)
    case False{}:
      problem_bl(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)

law body_in_bl:
  for +pt: B.Parts
  for +fa: List<&2, B.Contig>
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {PD.blank_st(L.body_in(pt, fa, o, PD.blank_st(st), l, at, inpos)) == PD.blank_st(L.body_in(pt, fa, o, st, l, at, inpos)) : R.RunSt}

def body_in_bl(pt, fa, st, o, l, at, inpos):
  match pt:
    case B.Whole{}:
      body_line_bl(L.judge(fa, B.Line.body(l)), st, o, l, at, inpos)
    case B.Pieces{+ps}:
      pieces_bl(ps, fa, o, st, B.Line.term(l), at, inpos)
    case B.Unsplit{+c}:
      unsplit_bl.k(L.stops(L.judge(fa, B.Line.body(l)), R.Opts.strict(o)), L.judge(fa, B.Line.body(l)), c, st, o, l, at, inpos)

law head_bl:
  for +isc: Bool
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  {PD.blank_st(R.head_line(isc, PD.blank_st(st), o, l)) == PD.blank_st(R.head_line(isc, st, o, l)) : R.RunSt}

def head_bl(isc, st, o, l):
  match isc st l:
    case True{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x} B.Line{+bd, +term}:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), blank_blank(la)) :
        {R.RunSt{n, True{}, "", c, e, _, b, k, h ++ R.added(o, term) ++ bd ++ term, ns, x} == PD.blank_st(R.head_line(True{}, R.RunSt{n, i, h, c, e, la, b, k, so, ns, x}, o, B.Line{bd, term})) : R.RunSt}
      {==}
    case False{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x} _:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), blank_blank(la)) :
        {R.RunSt{n, i, h ++ B.Line.text(l), c, e, _, b, k, so, ns, x} == PD.blank_st(R.head_line(False{}, R.RunSt{n, i, h, c, e, la, b, k, so, ns, x}, o, l)) : R.RunSt}
      {==}

# One line, the end, the whole run
# ================================

law step_bl:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  {PD.blank_st(L.line_step(fa, dfs, o, PD.blank_st(st), l)) == PD.blank_st(L.line_step(fa, dfs, o, st, l)) : R.RunSt}

def step_bl(dfs,fa, o, st, l):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, True{}}:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), blank_blank(la)) :
        {R.RunSt{n, i, h, c, e, _, b, k, so, ns, True{}} == R.RunSt{n, i, h, c, e, PD.blank(la), b, k, so, ns, True{}} : R.RunSt}
      {==}
    case R.RunSt{+n, False{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      head_bl(R.is_chrom_line(B.Line.body(l)), R.RunSt{1n+n, False{}, h, c, e, la, b, k, so, ns, False{}}, o, l)
    case R.RunSt{+n, True{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      +fs = B.Rec.fields(B.Line.body(l))
      body_in_bl(B.Rec.parts(dfs, o, B.Line.body(l)), fa, R.RunSt{1n+n, True{}, h, c, e, la, b, k, so, ns, False{}}, o, l,
        B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

law ff_bl:
  for +f: R.Flush
  for +o: String
  for +ns: List<&2, B.Note>
  for +k: R.Cnt
  {R.finish.flush(bF(f), o, ns, k) == R.finish.flush(f, o, ns, k) : R.Report}

def ff_bl(f, o, ns, k):
  match f k:
    case R.Flushed{+o2, +l2} R.Cnt{+a, +b, +c, +d}:
      {==}
    case R.Broke{+o2, +bad, +prev} _:
      {==}

law finish_bl:
  for +st: R.RunSt
  {R.finish(PD.blank_st(st)) == R.finish(st) : R.Report}

def finish_bl(st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, True{}}:
      {==}
    case R.RunSt{+n, False{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      {==}
    case R.RunSt{+n, True{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      Equal.trans(R.Report, R.finish.flush(R.flush(b, PD.blank(la)), so, ns, k), R.finish.flush(bF(R.flush(b, PD.blank(la))), so, ns, k), R.finish.flush(R.flush(b, la), so, ns, k),
        Equal.sym(R.Report, R.finish.flush(bF(R.flush(b, PD.blank(la))), so, ns, k), R.finish.flush(R.flush(b, PD.blank(la)), so, ns, k), ff_bl(R.flush(b, PD.blank(la)), so, ns, k)),
        %Equal.sym(R.Flush, bF(R.flush(b, PD.blank(la))), bF(R.flush(b, la)), flush_bl(b, la)) : {R.finish.flush(_, so, ns, k) == R.finish.flush(R.flush(b, la), so, ns, k) : R.Report}
        ff_bl(R.flush(b, la), so, ns, k))

# The report of a run from st is the report from st with last's text blanked.
law inv:
  for +dfs: B.Defs
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  {R.finish(L.run.go(ls, fa, dfs, o, PD.blank_st(st))) == R.finish(L.run.go(ls, fa, dfs, o, st)) : R.Report}

def inv(dfs,ls, fa, o, st):
  match ls:
    case Nil{}:
      finish_bl(st)
    case +l <> +t:
      +A = L.line_step(fa, dfs, o, PD.blank_st(st), l)
      +Bs = L.line_step(fa, dfs, o, st, l)
      Equal.trans(R.Report, R.finish(L.run.go(t, fa, dfs, o, A)), R.finish(L.run.go(t, fa, dfs, o, PD.blank_st(A))), R.finish(L.run.go(t, fa, dfs, o, Bs)),
        Equal.sym(R.Report, R.finish(L.run.go(t, fa, dfs, o, PD.blank_st(A))), R.finish(L.run.go(t, fa, dfs, o, A)), inv(dfs, t, fa, o, A)),
        Equal.trans(R.Report, R.finish(L.run.go(t, fa, dfs, o, PD.blank_st(A))), R.finish(L.run.go(t, fa, dfs, o, PD.blank_st(Bs))), R.finish(L.run.go(t, fa, dfs, o, Bs)),
          Equal.cong(R.RunSt, R.Report, z => R.finish(L.run.go(t, fa, dfs, o, z)), PD.blank_st(A), PD.blank_st(Bs), step_bl(dfs, fa, o, st, l)),
          inv(dfs, t, fa, o, Bs)))
