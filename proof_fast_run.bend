import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as N
import ./LAWS.bend as L
import ./proof_machine_nat.bend as PN

# Proofs: norm_run.bend's bookkeeping is run.bend's, up to the text of the
# last item written (N.blank_st), and the run's report does not depend on
# that text (inv).

def Items() -> Data:
  List<&2, R.Item>

# insert
# ======

law insert_go:
  for +t: List<&2, R.Item>
  for +le: Bool
  for +xk: Nat
  for +xp: Nat
  for +xa: B.At
  for +xs: String
  for +ek: Nat
  for +ep: Nat
  for +ea: B.At
  for +es: String
  for +hle: {Nat.is_le(xk, ek) == le : Bool}
  {N.insert.go(t, le, R.Item{xk, xp, xa, xs}, R.Item{ek, ep, ea, es}, ek) == R.insert(R.Item{ek, ep, ea, es}, R.Item{xk, xp, xa, xs} <> t) : List<&2, R.Item>}

def insert_go(t, le, xk, xp, xa, xs, ek, ep, ea, es, hle):
  match t le:
    case Nil{} True{}:
      +X = {R.Item{xk, xp, xa, xs} : R.Item}
      +E = {R.Item{ek, ep, ea, es} : R.Item}
      %Equal.sym(Bool, Nat.is_le(xk, ek), True{}, hle) :
        {X <> [E] == R.insert.put(_, X, E, Nil{}, [E]) : List<&2, R.Item>}
      {==}
    case Nil{} False{}:
      +X = {R.Item{xk, xp, xa, xs} : R.Item}
      +E = {R.Item{ek, ep, ea, es} : R.Item}
      %Equal.sym(Bool, Nat.is_le(xk, ek), False{}, hle) :
        {E <> X <> Nil{} == R.insert.put(_, X, E, Nil{}, [E]) : List<&2, R.Item>}
      {==}
    case R.Item{+yk, +yp, +ya, +ys} <> +t2 True{}:
      +X = {R.Item{xk, xp, xa, xs} : R.Item}
      +E = {R.Item{ek, ep, ea, es} : R.Item}
      +Y = {R.Item{yk, yp, ya, ys} : R.Item}
      %Equal.sym(Bool, Nat.is_le(xk, ek), True{}, hle) :
        {X <> N.insert.go(t2, Nat.is_le(yk, ek), Y, E, ek) == R.insert.put(_, X, E, Y <> t2, R.insert(E, Y <> t2)) : List<&2, R.Item>}
      %Equal.sym(Items(), N.insert.go(t2, Nat.is_le(yk, ek), Y, E, ek), R.insert(E, Y <> t2), insert_go(t2, Nat.is_le(yk, ek), yk, yp, ya, ys, ek, ep, ea, es, {==})) :
        {X <> _ == X <> R.insert(E, Y <> t2) : List<&2, R.Item>}
      {==}
    case R.Item{+yk, +yp, +ya, +ys} <> +t2 False{}:
      +X = {R.Item{xk, xp, xa, xs} : R.Item}
      +E = {R.Item{ek, ep, ea, es} : R.Item}
      +Y = {R.Item{yk, yp, ya, ys} : R.Item}
      %Equal.sym(Bool, Nat.is_le(xk, ek), False{}, hle) :
        {E <> X <> Y <> t2 == R.insert.put(_, X, E, Y <> t2, R.insert(E, Y <> t2)) : List<&2, R.Item>}
      {==}

law insert_eq:
  for +e: R.Item
  for +buf: List<&2, R.Item>
  {N.insert(e, buf) == R.insert(e, buf) : List<&2, R.Item>}

def insert_eq(e, buf):
  match e buf:
    case R.Item{+k, +p, +a, +s} Nil{}:
      {==}
    case R.Item{+k, +p, +a, +s} R.Item{+yk, +yp, +ya, +ys} <> +t:
      insert_go(t, Nat.is_le(yk, k), yk, yp, ya, ys, k, p, a, s, {==})

# take_ready and drop_ready in one pass
# =====================================

law ready_go:
  for +t: List<&2, R.Item>
  for +ok: Bool
  for +xk: Nat
  for +xp: Nat
  for +xa: B.At
  for +xs: String
  for +w: Nat
  for +inpos: Nat
  {N.ready.go(t, ok, R.Item{xk, xp, xa, xs}, w, inpos)
    == N.Two{R.take_ready.go(R.Item{xk, xp, xa, xs} <> t, ok, w, inpos), R.drop_ready.go(R.Item{xk, xp, xa, xs} <> t, ok, w, inpos)} : N.Two}

def ready_go(t, ok, xk, xp, xa, xs, w, inpos):
  match t ok:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case R.Item{+yk, +yp, +ya, +ys} <> +t2 True{}:
      +X = {R.Item{xk, xp, xa, xs} : R.Item}
      +Y = {R.Item{yk, yp, ya, ys} : R.Item}
      +b = Nat.is_le(Nat.add(yk, w), inpos)
      %Equal.sym(N.Two, N.ready.go(t2, b, Y, w, inpos), N.Two{R.take_ready.go(Y <> t2, b, w, inpos), R.drop_ready.go(Y <> t2, b, w, inpos)}, ready_go(t2, b, yk, yp, ya, ys, w, inpos)) :
        {N.two.k(X, _) == N.Two{X <> R.take_ready.go(Y <> t2, b, w, inpos), R.drop_ready.go(Y <> t2, b, w, inpos)} : N.Two}
      {==}
    case R.Item{+yk, +yp, +ya, +ys} <> +t2 False{}:
      {==}

law ready_eq:
  for +w: Nat
  for +inpos: Nat
  for +buf: List<&2, R.Item>
  {N.ready(w, inpos, buf) == N.Two{R.take_ready(w, inpos, buf), R.drop_ready(w, inpos, buf)} : N.Two}

def ready_eq(w, inpos, buf):
  match buf:
    case Nil{}:
      {==}
    case R.Item{+yk, +yp, +ya, +ys} <> +t:
      ready_go(t, Nat.is_le(Nat.add(yk, w), inpos), yk, yp, ya, ys, w, inpos)

# flush with the last item blanked
# ================================

def bF(f: R.Flush) -> R.Flush:
  match f:
    case R.Flushed{o, l}:
      R.Flushed{o, N.blank(l)}
    case R.Broke{o, b, p}:
      R.Broke{o, b, p}

law pre_bF:
  for +s: String
  for +f: R.Flush
  {bF(R.Flush.pre(s, f)) == R.Flush.pre(s, bF(f)) : R.Flush}

def pre_bF(s, f):
  match f:
    case R.Flushed{+o, +l}:
      {==}
    case R.Broke{+o, +b, +p}:
      {==}

law flush_go:
  for +t: List<&2, R.Item>
  for +ok: Bool
  for +xk: Nat
  for +xp: Nat
  for +xa: B.At
  for +xs: String
  for +L1: Maybe<&2, R.Item>
  for +L2: Maybe<&2, R.Item>
  for +hat: {R.at_of(L1) == R.at_of(L2) : Maybe<&2, B.At>}
  {N.flush.go(t, ok, R.Item{xk, xp, xa, xs}, L1) == bF(R.flush.put(ok, R.Item{xk, xp, xa, xs}, L2, R.flush(t, Some{R.Item{xk, xp, xa, xs}}))) : R.Flush}

def flush_go(t, ok, xk, xp, xa, xs, L1, L2, hat):
  match t ok:
    case Nil{} True{}:
      %Equal.sym(String, String.append(xs, ""), xs, PN.str_nil(xs)) :
        {R.Flushed{xs, Some{R.Item{xk, xp, xa, ""}}} == R.Flushed{_, Some{R.Item{xk, xp, xa, ""}}} : R.Flush}
      {==}
    case R.Item{+yk, +yp, +ya, +ys} <> +t2 True{}:
      +X = {R.Item{xk, xp, xa, xs} : R.Item}
      +Y = {R.Item{yk, yp, ya, ys} : R.Item}
      +F0 = R.flush.put(Nat.is_le(xk, yk), Y, Some{X}, R.flush(t2, Some{Y}))
      %Equal.sym(R.Flush, bF(R.Flush.pre(xs, F0)), R.Flush.pre(xs, bF(F0)), pre_bF(xs, F0)) :
        {R.Flush.pre(xs, N.flush.go(t2, Nat.is_le(xk, yk), Y, Some{R.Item{xk, xp, xa, ""}})) == _ : R.Flush}
      %Equal.sym(R.Flush, N.flush.go(t2, Nat.is_le(xk, yk), Y, Some{R.Item{xk, xp, xa, ""}}), bF(F0),
        flush_go(t2, Nat.is_le(xk, yk), yk, yp, ya, ys, Some{R.Item{xk, xp, xa, ""}}, Some{X}, {==})) :
        {R.Flush.pre(xs, _) == R.Flush.pre(xs, bF(F0)) : R.Flush}
      {==}
    case Nil{} False{}:
      %Equal.sym(Maybe<&2, B.At>, R.at_of(L1), R.at_of(L2), hat) : {R.Broke{"", xa, _} == R.Broke{"", xa, R.at_of(L2)} : R.Flush}
      {==}
    case R.Item{+yk, +yp, +ya, +ys} <> +t2 False{}:
      %Equal.sym(Maybe<&2, B.At>, R.at_of(L1), R.at_of(L2), hat) : {R.Broke{"", xa, _} == R.Broke{"", xa, R.at_of(L2)} : R.Flush}
      {==}

law flush_eq:
  for +items: List<&2, R.Item>
  for +L: Maybe<&2, R.Item>
  {N.flush(items, L) == bF(R.flush(items, L)) : R.Flush}

def flush_eq(items, L):
  match items:
    case Nil{}:
      {==}
    case R.Item{+k, +p, +a, +s} <> +t:
      flush_go(t, R.flush.ok(L, k), k, p, a, s, L, L, {==})

law blank_blank:
  for +L: Maybe<&2, R.Item>
  {N.blank(N.blank(L)) == N.blank(L) : Maybe<&2, R.Item>}

def blank_blank(L):
  match L:
    case None{}:
      {==}
    case Some{R.Item{+k, +p, +a, +t}}:
      {==}

law ok_blank:
  for +L: Maybe<&2, R.Item>
  for +k: Nat
  {R.flush.ok(N.blank(L), k) == R.flush.ok(L, k) : Bool}

def ok_blank(L, k):
  match L:
    case None{}:
      {==}
    case Some{R.Item{+lk, +p, +a, +t}}:
      {==}

law at_blank:
  for +L: Maybe<&2, R.Item>
  {R.at_of(N.blank(L)) == R.at_of(L) : Maybe<&2, B.At>}

def at_blank(L):
  match L:
    case None{}:
      {==}
    case Some{R.Item{+lk, +p, +a, +t}}:
      {==}

law flush_go_L:
  for +t: List<&2, R.Item>
  for +ok: Bool
  for +x: R.Item
  for +L1: Maybe<&2, R.Item>
  for +L2: Maybe<&2, R.Item>
  for +hat: {R.at_of(L1) == R.at_of(L2) : Maybe<&2, B.At>}
  {N.flush.go(t, ok, x, L1) == N.flush.go(t, ok, x, L2) : R.Flush}

def flush_go_L(t, ok, x, L1, L2, hat):
  match t ok x:
    case Nil{} True{} R.Item{+k, +p, +a, +s}:
      {==}
    case R.Item{+k2, +p2, +a2, +s2} <> +t2 True{} R.Item{+k, +p, +a, +s}:
      {==}
    case Nil{} False{} R.Item{+k, +p, +a, +s}:
      %Equal.sym(Maybe<&2, B.At>, R.at_of(L1), R.at_of(L2), hat) : {R.Broke{"", a, _} == R.Broke{"", a, R.at_of(L2)} : R.Flush}
      {==}
    case R.Item{+k2, +p2, +a2, +s2} <> +t2 False{} R.Item{+k, +p, +a, +s}:
      %Equal.sym(Maybe<&2, B.At>, R.at_of(L1), R.at_of(L2), hat) : {R.Broke{"", a, _} == R.Broke{"", a, R.at_of(L2)} : R.Flush}
      {==}

law flush_blank:
  for +items: List<&2, R.Item>
  for +L: Maybe<&2, R.Item>
  {N.flush(items, N.blank(L)) == N.flush(items, L) : R.Flush}

def flush_blank(items, L):
  match items:
    case Nil{}:
      %Equal.sym(Maybe<&2, R.Item>, N.blank(N.blank(L)), N.blank(L), blank_blank(L)) : {R.Flushed{"", _} == R.Flushed{"", N.blank(L)} : R.Flush}
      {==}
    case R.Item{+k, +p, +a, +s} <> +t:
      %Equal.sym(Bool, R.flush.ok(N.blank(L), k), R.flush.ok(L, k), ok_blank(L, k)) :
        {N.flush.go(t, _, R.Item{k, p, a, s}, N.blank(L)) == N.flush(R.Item{k, p, a, s} <> t, L) : R.Flush}
      flush_go_L(t, R.flush.ok(L, k), R.Item{k, p, a, s}, N.blank(L), L, at_blank(L))

# R.flush's result, up to its last's text, does not depend on last's text.
law flushF_bl:
  for +items: List<&2, R.Item>
  for +L: Maybe<&2, R.Item>
  {bF(R.flush(items, N.blank(L))) == bF(R.flush(items, L)) : R.Flush}

def flushF_bl(items, L):
  Equal.trans(R.Flush, bF(R.flush(items, N.blank(L))), N.flush(items, N.blank(L)), bF(R.flush(items, L)),
    Equal.sym(R.Flush, N.flush(items, N.blank(L)), bF(R.flush(items, N.blank(L))), flush_eq(items, N.blank(L))),
    Equal.trans(R.Flush, N.flush(items, N.blank(L)), N.flush(items, L), bF(R.flush(items, L)), flush_blank(items, L), flush_eq(items, L)))

# same_run, keyed, body_line
# ==========================

law emit_bl:
  for +f: R.Flush
  for +st: R.RunSt
  for +d: List<&2, R.Item>
  for +at: B.At
  {R.emit.ready(bF(f), N.blank_st(st), d, at) == N.blank_st(R.emit.ready(f, st, d, at)) : R.RunSt}

def emit_bl(f, st, d, at):
  match f st:
    case R.Flushed{+o2, +l2} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}
    case R.Broke{+o2, +bad, +prev} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law same_run_eq:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  {N.same_run(st, w, it) == N.blank_st(R.same_run(st, w, it)) : R.RunSt}

def same_run_eq(st, w, it):
  match st it:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x} R.Item{+key, +inpos, +at, +text}:
      +I = {R.Item{key, inpos, at, text} : R.Item}
      +St0 = {R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x} : R.RunSt}
      +St2 = {R.RunSt{n, i, h, c, e, N.blank(l), Nil{}, k, o, ns, x} : R.RunSt}
      +St = {R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} : R.RunSt}
      +bf = R.insert(I, b)
      %Equal.sym(Items(), N.insert(I, b), R.insert(I, b), insert_eq(I, b)) : {N.same_run.k(N.ready(w, inpos, _), St2, l, at) == N.blank_st(R.same_run(St, w, I)) : R.RunSt}
      %Equal.sym(N.Two, N.ready(w, inpos, bf), N.Two{R.take_ready(w, inpos, bf), R.drop_ready(w, inpos, bf)}, ready_eq(w, inpos, bf)) :
        {N.same_run.k(_, St2, l, at) == N.blank_st(R.same_run(St, w, I)) : R.RunSt}
      %Equal.sym(R.Flush, N.flush(R.take_ready(w, inpos, bf), l), bF(R.flush(R.take_ready(w, inpos, bf), l)), flush_eq(R.take_ready(w, inpos, bf), l)) :
        {R.emit.ready(_, St2, R.drop_ready(w, inpos, bf), at) == N.blank_st(R.same_run(St, w, I)) : R.RunSt}
      emit_bl(R.flush(R.take_ready(w, inpos, bf), l), St0, R.drop_ready(w, inpos, bf), at)

law keyed_go:
  for +same: Bool
  for +st2: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {N.keyed.go(same, st2, w, chrom, it) == N.blank_st(R.keyed.go(same, st2, w, chrom, it)) : R.RunSt}

def keyed_go(same, st2, w, chrom, it):
  match same:
    case True{}:
      same_run_eq(st2, w, it)
    case False{}:
      {==}

law keyed_eq:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  for +nts: List<&2, B.Note>
  for +k2: R.Cnt
  {N.keyed(st, w, it, nts, k2) == N.blank_st(R.keyed(st, w, it, nts, k2)) : R.RunSt}

def keyed_eq(st, w, it, nts, k2):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +chrom = R.Item.chrom(it)
      keyed_go(R.is_cur(c, chrom), R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, chrom, it)

law problem_eq:
  for +strict: Bool
  for +st: R.RunSt
  for +w: Nat
  for +c: B.Code
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {N.problem_line(strict, st, w, c, l, at, inpos) == N.blank_st(R.problem_line(strict, st, w, c, l, at, inpos)) : R.RunSt}

def problem_eq(strict, st, w, c, l, at, inpos):
  match strict:
    case True{}:
      {==}
    case False{}:
      keyed_eq(st, w, R.Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))

law body_line_eq:
  for +r: B.Res
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {N.body_line(r, st, o, l, at, inpos) == N.blank_st(R.body_line(r, st, o, l, at, inpos)) : R.RunSt}

def body_line_eq(r, st, o, l, at, inpos):
  match r:
    case B.Res{B.Broken{}, +k, +t, +s}:
      {==}
    case B.Res{B.NoContig{}, +k, +t, +s}:
      {==}
    case B.Res{B.Problem{+c}, +k, +t, +s}:
      problem_eq(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)
    case B.Res{B.Skipped{}, +k, +t, +s}:
      keyed_eq(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}))
    case B.Res{B.Normalized{}, +k, +t, +s}:
      keyed_eq(st, R.Opts.w(o), R.Item{k, inpos, at, t ++ B.Line.term(l)}, R.stale_note(s, at),
        R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))

# The machine's bookkeeping does not read last's text
# ===================================================

law srk_bl:
  for +t: N.Two
  for +st: R.RunSt
  for +L: Maybe<&2, R.Item>
  for +at: B.At
  {N.same_run.k(t, st, N.blank(L), at) == N.same_run.k(t, st, L, at) : R.RunSt}

def srk_bl(t, st, L, at):
  match t:
    case N.Two{+a, +d}:
      %Equal.sym(R.Flush, N.flush(a, N.blank(L)), N.flush(a, L), flush_blank(a, L)) :
        {R.emit.ready(_, st, d, at) == R.emit.ready(N.flush(a, L), st, d, at) : R.RunSt}
      {==}

law same_run_bl:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  {N.same_run(N.blank_st(st), w, it) == N.same_run(st, w, it) : R.RunSt}

def same_run_bl(st, w, it):
  match st it:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x} R.Item{+key, +inpos, +at, +text}:
      +T2 = N.ready(w, inpos, N.insert(R.Item{key, inpos, at, text}, b))
      %Equal.sym(Maybe<&2, R.Item>, N.blank(N.blank(l)), N.blank(l), blank_blank(l)) :
        {N.same_run.k(T2, R.RunSt{n, i, h, c, e, _, Nil{}, k, o, ns, x}, N.blank(l), at) == N.same_run(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, R.Item{key, inpos, at, text}) : R.RunSt}
      srk_bl(T2, R.RunSt{n, i, h, c, e, N.blank(l), Nil{}, k, o, ns, x}, l, at)

law stop_bl:
  for +st: R.RunSt
  for +out: String
  for +nt: B.Note
  {N.blank_st(R.stop(N.blank_st(st), out, nt)) == N.blank_st(R.stop(st, out, nt)) : R.RunSt}

def stop_bl(st, out, nt):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      %Equal.sym(Maybe<&2, R.Item>, N.blank(N.blank(l)), N.blank(l), blank_blank(l)) :
        {R.RunSt{n, i, h, c, e, _, b, k, String.append(o, out), List.append(&2, B.Note, ns, [nt]), True{}} == N.blank_st(R.stop(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, out, nt)) : R.RunSt}
      {==}

def NG(f: R.Flush, g: Bool, st: R.RunSt, +w: Nat, +chrom: String, +it: R.Item) -> R.RunSt:
  N.blank_st(R.new_run.go(f, g, st, w, chrom, it))

law ng:
  for +f: R.Flush
  for +g: Bool
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {NG(f, g, st, w, chrom, it) == NG(bF(f), g, N.blank_st(st), w, chrom, it) : R.RunSt}

def ng(f, g, st, w, chrom, it):
  match f g:
    case R.Broke{+o, +bad, +prev} _:
      Equal.sym(R.RunSt, N.blank_st(R.stop(N.blank_st(st), o, B.Stop{B.Unsorted{}, Some{bad}, prev})), N.blank_st(R.stop(st, o, B.Stop{B.Unsorted{}, Some{bad}, prev})),
        stop_bl(st, o, B.Stop{B.Unsorted{}, Some{bad}, prev}))
    case R.Flushed{+o2, +l2} True{}:
      Equal.sym(R.RunSt, N.blank_st(R.stop(N.blank_st(st), o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}})), N.blank_st(R.stop(st, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}})),
        stop_bl(st, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}))
    case R.Flushed{+o2, +l2} False{}:
      match st:
        case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
          {==}

law new_run_bl:
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {N.blank_st(R.new_run(N.blank_st(st), w, chrom, it)) == N.blank_st(R.new_run(st, w, chrom, it)) : R.RunSt}

def new_run_bl(st, w, chrom, it):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +g = R.has(chrom, e)
      +S0 = {R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} : R.RunSt}
      +S1 = {R.RunSt{n, i, h, c, e, N.blank(l), b, k, o, ns, x} : R.RunSt}
      +ef = flushF_bl(b, l)
      +es = Equal.cong(Maybe<&2, R.Item>, R.RunSt, z => R.RunSt{n, i, h, c, e, z, b, k, o, ns, x}, N.blank(N.blank(l)), N.blank(l), blank_blank(l))
      Equal.trans(R.RunSt, NG(R.flush(b, N.blank(l)), g, S1, w, chrom, it), NG(bF(R.flush(b, N.blank(l))), g, N.blank_st(S1), w, chrom, it), NG(R.flush(b, l), g, S0, w, chrom, it),
        ng(R.flush(b, N.blank(l)), g, S1, w, chrom, it),
        Equal.trans(R.RunSt, NG(bF(R.flush(b, N.blank(l))), g, N.blank_st(S1), w, chrom, it), NG(bF(R.flush(b, l)), g, N.blank_st(S0), w, chrom, it), NG(R.flush(b, l), g, S0, w, chrom, it),
          %ef : {NG(bF(R.flush(b, N.blank(l))), g, N.blank_st(S1), w, chrom, it) == NG(_, g, N.blank_st(S0), w, chrom, it) : R.RunSt}
          %es : {NG(bF(R.flush(b, N.blank(l))), g, N.blank_st(S1), w, chrom, it) == NG(bF(R.flush(b, N.blank(l))), g, _, w, chrom, it) : R.RunSt}
          {==},
          Equal.sym(R.RunSt, NG(R.flush(b, l), g, S0, w, chrom, it), NG(bF(R.flush(b, l)), g, N.blank_st(S0), w, chrom, it), ng(R.flush(b, l), g, S0, w, chrom, it))))

law keyed_go_bl:
  for +same: Bool
  for +st2: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {N.keyed.go(same, N.blank_st(st2), w, chrom, it) == N.keyed.go(same, st2, w, chrom, it) : R.RunSt}

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
  {N.keyed(N.blank_st(st), w, it, nts, k2) == N.keyed(st, w, it, nts, k2) : R.RunSt}

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
  {N.problem_line(strict, N.blank_st(st), w, c, l, at, inpos) == N.problem_line(strict, st, w, c, l, at, inpos) : R.RunSt}

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
  {N.body_line(r, N.blank_st(st), o, l, at, inpos) == N.body_line(r, st, o, l, at, inpos) : R.RunSt}

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

# The run's report does not depend on last's text
# ===============================================

law spec_bl:
  for +r: B.Res
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {N.blank_st(R.body_line(r, N.blank_st(st), o, l, at, inpos)) == N.blank_st(R.body_line(r, st, o, l, at, inpos)) : R.RunSt}

def spec_bl(r, st, o, l, at, inpos):
  +bs = N.blank_st(st)
  Equal.trans(R.RunSt, N.blank_st(R.body_line(r, bs, o, l, at, inpos)), N.body_line(r, bs, o, l, at, inpos), N.blank_st(R.body_line(r, st, o, l, at, inpos)),
    Equal.sym(R.RunSt, N.body_line(r, bs, o, l, at, inpos), N.blank_st(R.body_line(r, bs, o, l, at, inpos)), body_line_eq(r, bs, o, l, at, inpos)),
    Equal.trans(R.RunSt, N.body_line(r, bs, o, l, at, inpos), N.body_line(r, st, o, l, at, inpos), N.blank_st(R.body_line(r, st, o, l, at, inpos)),
      body_line_bl(r, st, o, l, at, inpos), body_line_eq(r, st, o, l, at, inpos)))

law head_bl:
  for +isc: Bool
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  {N.blank_st(R.head_line(isc, N.blank_st(st), o, l)) == N.blank_st(R.head_line(isc, st, o, l)) : R.RunSt}

def head_bl(isc, st, o, l):
  match isc st l:
    case True{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x} B.Line{+bd, +term}:
      %Equal.sym(Maybe<&2, R.Item>, N.blank(N.blank(la)), N.blank(la), blank_blank(la)) :
        {R.RunSt{n, True{}, "", c, e, _, b, k, h ++ R.added(o, term) ++ bd ++ term, ns, x} == N.blank_st(R.head_line(True{}, R.RunSt{n, i, h, c, e, la, b, k, so, ns, x}, o, B.Line{bd, term})) : R.RunSt}
      {==}
    case False{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x} _:
      %Equal.sym(Maybe<&2, R.Item>, N.blank(N.blank(la)), N.blank(la), blank_blank(la)) :
        {R.RunSt{n, i, h ++ B.Line.text(l), c, e, _, b, k, so, ns, x} == N.blank_st(R.head_line(False{}, R.RunSt{n, i, h, c, e, la, b, k, so, ns, x}, o, l)) : R.RunSt}
      {==}

law step_bl:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  {N.blank_st(L.line_step(fa, o, N.blank_st(st), l)) == N.blank_st(L.line_step(fa, o, st, l)) : R.RunSt}

def step_bl(fa, o, st, l):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, True{}}:
      %Equal.sym(Maybe<&2, R.Item>, N.blank(N.blank(la)), N.blank(la), blank_blank(la)) :
        {R.RunSt{n, i, h, c, e, _, b, k, so, ns, True{}} == R.RunSt{n, i, h, c, e, N.blank(la), b, k, so, ns, True{}} : R.RunSt}
      {==}
    case R.RunSt{+n, False{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      head_bl(R.is_chrom_line(B.Line.body(l)), R.RunSt{1n+n, False{}, h, c, e, la, b, k, so, ns, False{}}, o, l)
    case R.RunSt{+n, True{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      +fs = B.Rec.fields(B.Line.body(l))
      spec_bl(L.judge(fa, B.Line.body(l)), R.RunSt{1n+n, True{}, h, c, e, la, b, k, so, ns, False{}}, o, l,
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
  {R.finish(N.blank_st(st)) == R.finish(st) : R.Report}

def finish_bl(st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, True{}}:
      {==}
    case R.RunSt{+n, False{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      {==}
    case R.RunSt{+n, True{}, +h, +c, +e, +la, +b, +k, +so, +ns, False{}}:
      Equal.trans(R.Report, R.finish.flush(R.flush(b, N.blank(la)), so, ns, k), R.finish.flush(bF(R.flush(b, N.blank(la))), so, ns, k), R.finish.flush(R.flush(b, la), so, ns, k),
        Equal.sym(R.Report, R.finish.flush(bF(R.flush(b, N.blank(la))), so, ns, k), R.finish.flush(R.flush(b, N.blank(la)), so, ns, k), ff_bl(R.flush(b, N.blank(la)), so, ns, k)),
        %Equal.sym(R.Flush, bF(R.flush(b, N.blank(la))), bF(R.flush(b, la)), flushF_bl(b, la)) : {R.finish.flush(_, so, ns, k) == R.finish.flush(R.flush(b, la), so, ns, k) : R.Report}
        ff_bl(R.flush(b, la), so, ns, k))

# The report of a run from st is the report from st with last's text blanked.
law inv:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  {R.finish(L.run.go(ls, fa, o, N.blank_st(st))) == R.finish(L.run.go(ls, fa, o, st)) : R.Report}

def inv(ls, fa, o, st):
  match ls:
    case Nil{}:
      finish_bl(st)
    case +l <> +t:
      +A = L.line_step(fa, o, N.blank_st(st), l)
      +Bs = L.line_step(fa, o, st, l)
      Equal.trans(R.Report, R.finish(L.run.go(t, fa, o, A)), R.finish(L.run.go(t, fa, o, N.blank_st(A))), R.finish(L.run.go(t, fa, o, Bs)),
        Equal.sym(R.Report, R.finish(L.run.go(t, fa, o, N.blank_st(A))), R.finish(L.run.go(t, fa, o, A)), inv(t, fa, o, A)),
        Equal.trans(R.Report, R.finish(L.run.go(t, fa, o, N.blank_st(A))), R.finish(L.run.go(t, fa, o, N.blank_st(Bs))), R.finish(L.run.go(t, fa, o, Bs)),
          Equal.cong(R.RunSt, R.Report, z => R.finish(L.run.go(t, fa, o, z)), N.blank_st(A), N.blank_st(Bs), step_bl(fa, o, st, l)),
          inv(t, fa, o, Bs)))
