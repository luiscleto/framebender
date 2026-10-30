import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_b_budget_dig.bend as G
import ./proof_b_budget_rec.bend as Q
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The output-length lemma (notes/bytes_proofs_budget.md): a run writes at most
# 2 (63 (|vcf| + 1) + 61 + |args text|) bytes.
#
# Invariant: the bytes held (buffer texts, header, output) stay within an
# allowance that grows by 21 (|line| + 1) per line; the two added header lines
# have their own allowance AD(o) until the #CHROM line. A stop writes the
# buffer once more, so a stopped run's output is within twice the allowance.

def SL(+s: String) -> Nat:
  String.length(s)

# ---------------------------------------------------------------------------
# Buffers and flushes
# ---------------------------------------------------------------------------

def BS(xs: List<&2, R.Item>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(SL(R.Item.text(x)), BS(t))

def ins.k(le: Bool, +x: R.Item, +e: R.Item, +t: List<&2, R.Item>, +ins: List<&2, R.Item>,
  +ih: {BS(ins) == Nat.add(SL(R.Item.text(e)), BS(t)) : Nat}) ->
  {BS(R.insert.put(le, x, e, t, ins)) == Nat.add(SL(R.Item.text(e)), BS(x <> t)) : Nat}:
  match le:
    case True{}:
      Equal.trans(Nat, Nat.add(SL(R.Item.text(x)), BS(ins)), Nat.add(SL(R.Item.text(x)), Nat.add(SL(R.Item.text(e)), BS(t))),
        Nat.add(SL(R.Item.text(e)), Nat.add(SL(R.Item.text(x)), BS(t))),
        Equal.cong(Nat, Nat, z => Nat.add(SL(R.Item.text(x)), z), BS(ins), Nat.add(SL(R.Item.text(e)), BS(t)), ih),
        N.add_left_comm(SL(R.Item.text(x)), SL(R.Item.text(e)), BS(t)))
    case False{}:
      {==}

def ins_bs(+e: R.Item, buf: List<&2, R.Item>) -> {BS(R.insert(e, buf)) == Nat.add(SL(R.Item.text(e)), BS(buf)) : Nat}:
  match buf:
    case Nil{}:
      {==}
    case +x <> +t:
      ins.k(Nat.is_le(R.Item.key(x), R.Item.key(e)), x, e, t, R.insert(e, t), ins_bs(e, t))

def td_bs(buf: List<&2, R.Item>, ok: Bool, +w: Nat, +ip: Nat) ->
  {Nat.add(BS(R.take_ready.go(buf, ok, w, ip)), BS(R.drop_ready.go(buf, ok, w, ip))) == BS(buf) : Nat}:
  match buf ok:
    case Nil{} _:
      {==}
    case +x <> +t True{}:
      +A = BS(R.take_ready.go(t, R.head_ready(w, ip, t), w, ip))
      +D = BS(R.drop_ready.go(t, R.head_ready(w, ip, t), w, ip))
      Equal.trans(Nat, Nat.add(Nat.add(SL(R.Item.text(x)), A), D), Nat.add(SL(R.Item.text(x)), Nat.add(A, D)), Nat.add(SL(R.Item.text(x)), BS(t)),
        N.add_assoc(SL(R.Item.text(x)), A, D),
        Equal.cong(Nat, Nat, z => Nat.add(SL(R.Item.text(x)), z), Nat.add(A, D), BS(t), td_bs(t, R.head_ready(w, ip, t), w, ip)))
    case x <> t False{}:
      {==}

def FO(f: R.Flush) -> String:
  match f:
    case R.Flushed{o, l}:
      o
    case R.Broke{o, b, p}:
      o

def pre_fo(+s: String, f: R.Flush) -> {SL(FO(R.Flush.pre(s, f))) == Nat.add(SL(s), SL(FO(f))) : Nat}:
  match f:
    case R.Flushed{+o, l}:
      G.slen_app(s, o)
    case R.Broke{+o, b, p}:
      G.slen_app(s, o)

def fl.k(ok: Bool, +x: R.Item, last: Maybe<&2, R.Item>, +rest: R.Flush, +t: List<&2, R.Item>, +ih: {Nat.is_le(SL(FO(rest)), BS(t)) == True{} : Bool}) ->
  {Nat.is_le(SL(FO(R.flush.put(ok, x, last, rest))), BS(x <> t)) == True{} : Bool}:
  match ok:
    case True{}:
      AB.subst(Nat, z => {Nat.is_le(z, BS(x <> t)) == True{} : Bool}, Nat.add(SL(R.Item.text(x)), SL(FO(rest))), SL(FO(R.Flush.pre(R.Item.text(x), rest))),
        Equal.sym(Nat, SL(FO(R.Flush.pre(R.Item.text(x), rest))), Nat.add(SL(R.Item.text(x)), SL(FO(rest))), pre_fo(R.Item.text(x), rest)),
        N.le_add_mono_l(SL(R.Item.text(x)), SL(FO(rest)), BS(t), ih))
    case False{}:
      N.le_zero_l(BS(x <> t))

# What a flush writes is at most the items' texts.
def fl_le(xs: List<&2, R.Item>, +last: Maybe<&2, R.Item>) -> {Nat.is_le(SL(FO(R.flush(xs, last))), BS(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      fl.k(R.flush.ok(last, R.Item.key(x)), x, last, R.flush(t, Some{x}), t, fl_le(t, Some{x}))

# ---------------------------------------------------------------------------
# The lines of a file: sum of (1 + |text|) is at most 3 (|s| + 1)
# ---------------------------------------------------------------------------

def LT(ls: List<&2, B.Line>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case l <> t:
      1n+Nat.add(SL(B.Line.text(l)), LT(t))

def take_sl(s: String, +n: Nat) -> {Nat.is_le(SL(String.take(s, n)), SL(s)) == True{} : Bool}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{h, +t} 0n:
      N.le_zero_l(1n+SL(t))
    case SCon{h, +t} 1n+p:
      take_sl(t, p)

def line_sl.if(cr: Bool, +p: String) -> {Nat.is_le(SL(B.Line.text(B.Text.line.if(cr, p))), 2n+SL(p)) == True{} : Bool}:
  match cr:
    case True{}:
      +u = String.take(p, Nat.sub(SL(p), 1n))
      AB.subst(Nat, z => {Nat.is_le(z, 2n+SL(p)) == True{} : Bool}, Nat.add(SL(u), 2n), SL(u ++ "\r\n"), Equal.sym(Nat, SL(u ++ "\r\n"), Nat.add(SL(u), 2n), G.slen_app(u, "\r\n")),
        AB.subst(Nat, z => {Nat.is_le(z, 2n+SL(p)) == True{} : Bool}, 2n+SL(u), Nat.add(SL(u), 2n), N.add_comm(2n, SL(u)), take_sl(p, Nat.sub(SL(p), 1n))))
    case False{}:
      AB.subst(Nat, z => {Nat.is_le(z, 2n+SL(p)) == True{} : Bool}, Nat.add(SL(p), 1n), SL(p ++ "\n"), Equal.sym(Nat, SL(p ++ "\n"), Nat.add(SL(p), 1n), G.slen_app(p, "\n")),
        AB.subst(Nat, z => {Nat.is_le(z, 2n+SL(p)) == True{} : Bool}, 1n+SL(p), Nat.add(SL(p), 1n), Equal.sym(Nat, Nat.add(SL(p), 1n), 1n+SL(p), N.add_one(SL(p))), N.le_add_l(1n+SL(p), 1n)))

def line_sl(+p: String) -> {Nat.is_le(SL(B.Line.text(B.Text.line(p))), 2n+SL(p)) == True{} : Bool}:
  line_sl.if(String.ends_with(p, "\r"), p)

# 3 + x <= 3 (1 + x).
def three(+x: Nat) -> {Nat.is_le(3n+x, Nat.mul(3n, 1n+x)) == True{} : Bool}:
  +y = Nat.mul(2n, 1n+x)
  +hy = N.le_trans(1n, Nat.add(1n+x, 0n), Nat.add(x, Nat.add(1n+x, 0n)), N.le_zero_l(Nat.add(x, 0n)), N.le_add_l(Nat.add(1n+x, 0n), x))
  AB.subst(Nat, z => {Nat.is_le(z, Nat.add(x, y)) == True{} : Bool}, Nat.add(x, 2n), Nat.add(2n, x), N.add_comm(x, 2n), N.le_add_mono_l(x, 2n, y, hy))

def last_lt(+p: String) -> {Nat.is_le(LT(B.Text.last(p)), Nat.mul(3n, Q.SN([p]))) == True{} : Bool}:
  match p:
    case SNil{}:
      N.le_zero_l(Nat.mul(3n, Q.SN([SNil{}])))
    case SCon{+h, +t}:
      +P0 = {SCon{h, t} : String}
      +T0 = SL(B.Line.text(B.Text.line(P0)))
      +a = N.le_trans(1n+Nat.add(T0, 0n), 3n+SL(P0), Nat.mul(3n, 1n+SL(P0)),
        AB.subst(Nat, z => {Nat.is_le(1n+z, 3n+SL(P0)) == True{} : Bool}, T0, Nat.add(T0, 0n), Equal.sym(Nat, Nat.add(T0, 0n), T0, N.add_zero(T0)), line_sl(P0)),
        three(SL(P0)))
      AB.subst(Nat, z => {Nat.is_le(1n+Nat.add(T0, 0n), Nat.mul(3n, 1n+z)) == True{} : Bool}, SL(P0), Nat.add(SL(P0), 0n), Equal.sym(Nat, Nat.add(SL(P0), 0n), SL(P0), N.add_zero(SL(P0))), a)

def lg(ps: List<&2, String>, +p: String) -> {Nat.is_le(LT(B.Text.lines.go(ps, p)), Nat.mul(3n, Q.SN(p <> ps))) == True{} : Bool}:
  match ps:
    case Nil{}:
      last_lt(p)
    case +q <> +t:
      +T0 = SL(B.Line.text(B.Text.line(p)))
      +M = Nat.mul(3n, Q.SN(q <> t))
      +L0 = LT(B.Text.lines.go(t, q))
      +h1 = P.le_add(1n+T0, 3n+SL(p), L0, M, line_sl(p), lg(t, q))
      +h2 = N.le_trans(Nat.add(1n+T0, L0), Nat.add(3n+SL(p), M), Nat.add(Nat.mul(3n, 1n+SL(p)), M), h1, N.le_add_mono_r(M, 3n+SL(p), Nat.mul(3n, 1n+SL(p)), three(SL(p))))
      AB.subst(Nat, z => {Nat.is_le(Nat.add(1n+T0, L0), z) == True{} : Bool}, Nat.add(Nat.mul(3n, 1n+SL(p)), M), Nat.mul(3n, Nat.add(1n+SL(p), Q.SN(q <> t))),
        Equal.sym(Nat, Nat.mul(3n, Nat.add(1n+SL(p), Q.SN(q <> t))), Nat.add(Nat.mul(3n, 1n+SL(p)), M), N.mul_add(3n, 1n+SL(p), Q.SN(q <> t))), h2)

def ls_start(ps: List<&2, String>) -> {Nat.is_le(LT(B.Text.lines.start(ps)), Nat.mul(3n, Q.SN(ps))) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      lg(t, p)

# The lines of s: their texts plus one per line, at most 3 (|s| + 1).
def lines_lt(+s: String) -> {Nat.is_le(LT(B.Text.lines(s)), Nat.mul(3n, 1n+SL(s))) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(LT(B.Text.lines(s)), Nat.mul(3n, z)) == True{} : Bool}, Q.SN(String.split(s, '\n')), 1n+SL(s), Q.split_sn(s, '\n'), ls_start(String.split(s, '\n')))

# ---------------------------------------------------------------------------
# The two added header lines: 61 bytes, the arguments, two terminators
# ---------------------------------------------------------------------------

def AD(o: B.Opts) -> Nat:
  match o:
    case B.Opts{s, w, args}:
      Nat.add(61n, SL(R.args_text(args)))

def ad_len(o: B.Opts, +term: String) -> {Nat.is_le(SL(R.added(o, term)), Nat.add(AD(o), Nat.add(SL(term), SL(term)))) == True{} : Bool}:
  match o:
    case B.Opts{s, w, +args}:
      +T0 = SL(term)
      +A0 = SL(R.args_text(args))
      +X0 = "##framebender_normCommand=norm" ++ (R.args_text(args) ++ term)
      +e1 = Equal.trans(Nat, SL(term ++ X0), Nat.add(T0, SL(X0)), Nat.add(T0, 30n+Nat.add(A0, T0)), G.slen_app(term, X0),
        Equal.cong(Nat, Nat, z => Nat.add(T0, 30n+z), SL(R.args_text(args) ++ term), Nat.add(A0, T0), G.slen_app(R.args_text(args), term)))
      +e2 = Equal.trans(Nat, SL(term ++ X0), Nat.add(T0, 30n+Nat.add(A0, T0)), Nat.add(30n+Nat.add(A0, T0), T0), e1, N.add_comm(T0, 30n+Nat.add(A0, T0)))
      +e3 = Equal.trans(Nat, SL(term ++ X0), 30n+Nat.add(Nat.add(A0, T0), T0), 30n+Nat.add(A0, Nat.add(T0, T0)), e2,
        Equal.cong(Nat, Nat, z => 30n+z, Nat.add(Nat.add(A0, T0), T0), Nat.add(A0, Nat.add(T0, T0)), N.add_assoc(A0, T0, T0)))
      AB.subst(Nat, z => {Nat.is_le(31n+z, 61n+Nat.add(A0, Nat.add(T0, T0))) == True{} : Bool}, 30n+Nat.add(A0, Nat.add(T0, T0)), SL(term ++ X0),
        Equal.sym(Nat, SL(term ++ X0), 30n+Nat.add(A0, Nat.add(T0, T0)), e3), N.le_refl(61n+Nat.add(A0, Nat.add(T0, T0))))

# ---------------------------------------------------------------------------
# The invariant
# ---------------------------------------------------------------------------

def WSt(+b: List<&2, R.Item>, +h: String, +o: String) -> Nat:
  Nat.add(BS(b), Nat.add(SL(h), SL(o)))

# Halted: the output is within twice the allowance. Else the bytes held are
# within it, leaving A for the added lines while the header is read.
def INV(st: R.RunSt, +X: Nat, +A: Nat) -> Type:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      match i x:
        case _ True{}:
          {Nat.is_le(SL(o), Nat.add(X, X)) == True{} : Bool}
        case True{} False{}:
          {Nat.is_le(WSt(b, h, o), X) == True{} : Bool}
        case False{} False{}:
          {Nat.is_le(Nat.add(WSt(b, h, o), A), X) == True{} : Bool}

# After one body line: halted with the output within Y, or in the body with
# the bytes held within Y.
def POST(st: R.RunSt, +Y: Nat) -> Type:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      match i x:
        case _ True{}:
          {Nat.is_le(SL(o), Y) == True{} : Bool}
        case True{} False{}:
          {Nat.is_le(WSt(b, h, o), Y) == True{} : Bool}
        case False{} False{}:
          Empty

def post_mono(st: R.RunSt, +Y: Nat, +Y2: Nat, h: POST(st, Y), +hy: {Nat.is_le(Y, Y2) == True{} : Bool}) -> POST(st, Y2):
  match st:
    case R.RunSt{n, i, +h0, c, e, l, +b, k, +o, ns, x}:
      match i x:
        case _ True{}:
          N.le_trans(SL(o), Y, Y2, h, hy)
        case True{} False{}:
          N.le_trans(WSt(b, h0, o), Y, Y2, h, hy)
        case False{} False{}:
          h

def post_inv(st: R.RunSt, +Y: Nat, +X: Nat, +A: Nat, h: POST(st, Y), +hy: {Nat.is_le(Y, X) == True{} : Bool}) -> INV(st, X, A):
  match st:
    case R.RunSt{n, i, +h0, c, e, l, +b, k, +o, ns, x}:
      match i x:
        case _ True{}:
          N.le_trans(SL(o), X, Nat.add(X, X), N.le_trans(SL(o), Y, X, h, hy), N.le_add_r(X, X))
        case True{} False{}:
          N.le_trans(WSt(b, h0, o), Y, X, h, hy)
        case False{} False{}:
          Empty.absurd({Nat.is_le(Nat.add(WSt(b, h0, o), A), X) == True{} : Bool}, h)

# ---------------------------------------------------------------------------
# One body line
# ---------------------------------------------------------------------------

def RS(+n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>) -> R.RunSt:
  R.RunSt{n, True{}, h, c, e, l, b, k, o, ns, False{}}

# o ++ o2 with o2 at most Z: at most Z + held bytes.
def app_le(+o: String, +o2: String, +b: List<&2, R.Item>, +h: String, +Z: Nat, +hz: {Nat.is_le(SL(o2), Z) == True{} : Bool}) -> {Nat.is_le(SL(o ++ o2), Nat.add(Z, Nat.add(SL(h), SL(o)))) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Z, Nat.add(SL(h), SL(o)))) == True{} : Bool}, Nat.add(SL(o2), SL(o)), SL(o ++ o2),
    Equal.trans(Nat, Nat.add(SL(o2), SL(o)), Nat.add(SL(o), SL(o2)), SL(o ++ o2), N.add_comm(SL(o2), SL(o)), Equal.sym(Nat, SL(o ++ o2), Nat.add(SL(o), SL(o2)), G.slen_app(o, o2))),
    N.le_trans(Nat.add(SL(o2), SL(o)), Nat.add(Z, SL(o)), Nat.add(Z, Nat.add(SL(h), SL(o))), N.le_add_mono_r(SL(o), SL(o2), Z, hz),
      N.le_add_mono_l(Z, SL(o), Nat.add(SL(h), SL(o)), N.le_add_l(SL(o), SL(h)))))

def ar1(+r: Nat, +h: Nat, +o: Nat, +o2: Nat) -> {Nat.add(r, Nat.add(h, Nat.add(o, o2))) == Nat.add(Nat.add(o2, r), Nat.add(h, o)) : Nat}:
  Equal.trans(Nat, Nat.add(r, Nat.add(h, Nat.add(o, o2))), Nat.add(r, Nat.add(h, Nat.add(o2, o))), Nat.add(Nat.add(o2, r), Nat.add(h, o)),
    Equal.cong(Nat, Nat, z => Nat.add(r, Nat.add(h, z)), Nat.add(o, o2), Nat.add(o2, o), N.add_comm(o, o2)),
    Equal.trans(Nat, Nat.add(r, Nat.add(h, Nat.add(o2, o))), Nat.add(r, Nat.add(o2, Nat.add(h, o))), Nat.add(Nat.add(o2, r), Nat.add(h, o)),
      Equal.cong(Nat, Nat, z => Nat.add(r, z), Nat.add(h, Nat.add(o2, o)), Nat.add(o2, Nat.add(h, o)), N.add_left_comm(h, o2, o)),
      Equal.trans(Nat, Nat.add(r, Nat.add(o2, Nat.add(h, o))), Nat.add(o2, Nat.add(r, Nat.add(h, o))), Nat.add(Nat.add(o2, r), Nat.add(h, o)),
        N.add_left_comm(r, o2, Nat.add(h, o)), Equal.sym(Nat, Nat.add(Nat.add(o2, r), Nat.add(h, o)), Nat.add(o2, Nat.add(r, Nat.add(h, o))), N.add_assoc(o2, r, Nat.add(h, o))))))

def em(f: R.Flush, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +rest: List<&2, R.Item>, +at: B.At, +Z: Nat, +hf: {Nat.is_le(Nat.add(SL(FO(f)), BS(rest)), Z) == True{} : Bool}) ->
  POST(R.emit.ready(f, RS(n, h, c, e, l, Nil{}, k, o, ns), rest, at), Nat.add(Z, Nat.add(SL(h), SL(o)))):
  match f:
    case R.Broke{+o2, bad, prev}:
      app_le(o, o2, Nil{}, h, Z, N.le_trans(SL(o2), Nat.add(SL(o2), BS(rest)), Z, N.le_add_r(SL(o2), BS(rest)), hf))
    case R.Flushed{+o2, l2}:
      +e1 = Equal.trans(Nat, WSt(rest, h, o ++ o2), Nat.add(BS(rest), Nat.add(SL(h), Nat.add(SL(o), SL(o2)))), Nat.add(Nat.add(SL(o2), BS(rest)), Nat.add(SL(h), SL(o))),
        Equal.cong(Nat, Nat, z => Nat.add(BS(rest), Nat.add(SL(h), z)), SL(o ++ o2), Nat.add(SL(o), SL(o2)), G.slen_app(o, o2)),
        ar1(BS(rest), SL(h), SL(o), SL(o2)))
      AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Z, Nat.add(SL(h), SL(o)))) == True{} : Bool}, Nat.add(Nat.add(SL(o2), BS(rest)), Nat.add(SL(h), SL(o))), WSt(rest, h, o ++ o2),
        Equal.sym(Nat, WSt(rest, h, o ++ o2), Nat.add(Nat.add(SL(o2), BS(rest)), Nat.add(SL(h), SL(o))), e1),
        N.le_add_mono_r(Nat.add(SL(h), SL(o)), Nat.add(SL(o2), BS(rest)), Z, hf))

def sr(+n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +w: Nat, +key: Nat, +ip: Nat, +at: B.At, +t: String) ->
  POST(R.same_run(RS(n, h, c, e, l, b, k, o, ns), w, R.Item{key, ip, at, t}), Nat.add(SL(t), WSt(b, h, o))):
  +it = {R.Item{key, ip, at, t} : R.Item}
  +buf = R.insert(it, b)
  +ok = R.head_ready(w, ip, buf)
  +tk = R.take_ready.go(buf, ok, w, ip)
  +dr = R.drop_ready.go(buf, ok, w, ip)
  +hf = AB.subst(Nat, z => {Nat.is_le(Nat.add(SL(FO(R.flush(tk, l))), BS(dr)), z) == True{} : Bool}, Nat.add(BS(tk), BS(dr)), BS(buf), td_bs(buf, ok, w, ip),
    N.le_add_mono_r(BS(dr), SL(FO(R.flush(tk, l))), BS(tk), fl_le(tk, l)))
  P0 = em(R.flush(tk, l), n, h, c, e, l, k, o, ns, dr, at, BS(buf), hf)
  +e1 = Equal.trans(Nat, Nat.add(BS(buf), Nat.add(SL(h), SL(o))), Nat.add(Nat.add(SL(t), BS(b)), Nat.add(SL(h), SL(o))), Nat.add(SL(t), WSt(b, h, o)),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(SL(h), SL(o))), BS(buf), Nat.add(SL(t), BS(b)), ins_bs(it, b)),
    N.add_assoc(SL(t), BS(b), Nat.add(SL(h), SL(o))))
  AB.subst(Nat, z => POST(R.emit.ready(R.flush(tk, l), RS(n, h, c, e, l, Nil{}, k, o, ns), dr, at), z), Nat.add(BS(buf), Nat.add(SL(h), SL(o))), Nat.add(SL(t), WSt(b, h, o)), e1, P0)

# A stop writing o2 (at most the buffer).
def stop_le(+n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +o2: String, +nt: B.Note, +t: String, +h2: {Nat.is_le(SL(o2), BS(b)) == True{} : Bool}) -> POST(R.stop(RS(n, h, c, e, l, b, k, o, ns), o2, nt), Nat.add(SL(t), WSt(b, h, o))):
  N.le_trans(SL(o ++ o2), WSt(b, h, o), Nat.add(SL(t), WSt(b, h, o)), app_le(o, o2, b, h, BS(b), h2), N.le_add_l(WSt(b, h, o), SL(t)))

def nr.k(f: R.Flush, again: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +w: Nat, +chrom: String, +key: Nat, +ip: Nat, +at: B.At, +t: String, +hf: {Nat.is_le(SL(FO(f)), BS(b)) == True{} : Bool}) ->
  POST(R.new_run.go(f, again, RS(n, h, c, e, l, b, k, o, ns), w, chrom, R.Item{key, ip, at, t}), Nat.add(SL(t), WSt(b, h, o))):
  match f again:
    case R.Broke{+o2, +bad, +prev} _:
      stop_le(n, h, c, e, l, b, k, o, ns, o2, B.Stop{B.Unsorted{}, Some{bad}, prev}, t, hf)
    case R.Flushed{+o2, l2} True{}:
      stop_le(n, h, c, e, l, b, k, o, ns, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(R.Item{key, ip, at, t})}, None{}}, t, hf)
    case R.Flushed{+o2, l2} False{}:
      +W2 = WSt(Nil{}, h, o ++ o2)
      +e1 = Equal.trans(Nat, W2, Nat.add(SL(h), Nat.add(SL(o), SL(o2))), Nat.add(SL(o2), Nat.add(SL(h), SL(o))),
        Equal.cong(Nat, Nat, z => Nat.add(SL(h), z), SL(o ++ o2), Nat.add(SL(o), SL(o2)), G.slen_app(o, o2)),
        Equal.trans(Nat, Nat.add(SL(h), Nat.add(SL(o), SL(o2))), Nat.add(SL(h), Nat.add(SL(o2), SL(o))), Nat.add(SL(o2), Nat.add(SL(h), SL(o))),
          Equal.cong(Nat, Nat, z => Nat.add(SL(h), z), Nat.add(SL(o), SL(o2)), Nat.add(SL(o2), SL(o)), N.add_comm(SL(o), SL(o2))),
          N.add_left_comm(SL(h), SL(o2), SL(o))))
      +h1 = AB.subst(Nat, z => {Nat.is_le(z, WSt(b, h, o)) == True{} : Bool}, Nat.add(SL(o2), Nat.add(SL(h), SL(o))), W2, Equal.sym(Nat, W2, Nat.add(SL(o2), Nat.add(SL(h), SL(o))), e1),
        N.le_add_mono_r(Nat.add(SL(h), SL(o)), SL(o2), BS(b), hf))
      post_mono(R.same_run(RS(n, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o ++ o2, ns), w, R.Item{key, ip, at, t}), Nat.add(SL(t), W2), Nat.add(SL(t), WSt(b, h, o)),
        sr(n, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o ++ o2, ns, w, key, ip, at, t), N.le_add_mono_l(SL(t), W2, WSt(b, h, o), h1))

def nr(+n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +w: Nat, +chrom: String, +key: Nat, +ip: Nat, +at: B.At, +t: String) ->
  POST(R.new_run(RS(n, h, c, e, l, b, k, o, ns), w, chrom, R.Item{key, ip, at, t}), Nat.add(SL(t), WSt(b, h, o))):
  nr.k(R.flush(b, l), R.has(chrom, e), n, h, c, e, l, b, k, o, ns, w, chrom, key, ip, at, t, fl_le(b, l))

def ky.k(same: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +w: Nat, +chrom: String, +key: Nat, +ip: Nat, +at: B.At, +t: String) ->
  POST(R.keyed.go(same, RS(n, h, c, e, l, b, k, o, ns), w, chrom, R.Item{key, ip, at, t}), Nat.add(SL(t), WSt(b, h, o))):
  match same:
    case True{}:
      sr(n, h, c, e, l, b, k, o, ns, w, key, ip, at, t)
    case False{}:
      nr(n, h, c, e, l, b, k, o, ns, w, chrom, key, ip, at, t)

def ky(+n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +w: Nat, +key: Nat, +ip: Nat, +at: B.At, +t: String, +nts: List<&2, B.Note>, +k2: R.Cnt) ->
  POST(R.keyed(RS(n, h, c, e, l, b, k, o, ns), w, R.Item{key, ip, at, t}, nts, k2), Nat.add(SL(t), WSt(b, h, o))):
  +chrom = R.Item.chrom(R.Item{key, ip, at, t})
  ky.k(R.is_cur(c, chrom), n, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), w, chrom, key, ip, at, t)

def LC(+tx: String) -> Nat:
  G.LIN(21n, 0n, 1n+SL(tx))

def lc_ge(+tx: String) -> {Nat.is_le(SL(tx), LC(tx)) == True{} : Bool}:
  N.le_trans(SL(tx), 1n+SL(tx), LC(tx), N.le_add_l(SL(tx), 1n), N.le_add_r(1n+SL(tx), G.LIN(20n, 0n, 1n+SL(tx))))

# A normalized record (judge's bound) with its terminator.
def lc_n(+bd: String, +term: String, +t: String, +h: {Nat.is_le(SL(t), G.LIN(10n, 10n, 1n+SL(bd))) == True{} : Bool}) -> {Nat.is_le(Nat.add(SL(t), SL(term)), LC(bd ++ term)) == True{} : Bool}:
  +y = {1n+SL(bd ++ term) : Nat}
  +ey = G.slen_app(bd, term)
  +hb = AB.subst(Nat, z => {Nat.is_le(1n+SL(bd), 1n+z) == True{} : Bool}, Nat.add(SL(bd), SL(term)), SL(bd ++ term), Equal.sym(Nat, SL(bd ++ term), Nat.add(SL(bd), SL(term)), ey),
    N.le_add_r(SL(bd), SL(term)))
  +ht = N.le_trans(SL(term), SL(bd ++ term), y,
    AB.subst(Nat, z => {Nat.is_le(SL(term), z) == True{} : Bool}, Nat.add(SL(bd), SL(term)), SL(bd ++ term), Equal.sym(Nat, SL(bd ++ term), Nat.add(SL(bd), SL(term)), ey), N.le_add_l(SL(term), SL(bd))),
    N.le_add_l(SL(bd ++ term), 1n))
  +h1 = N.le_trans(SL(t), G.LIN(10n, 10n, 1n+SL(bd)), G.LIN(10n, 10n, y), h, G.lin_x(10n, 10n, 1n+SL(bd), y, hb))
  +h2 = G.lin_add(SL(t), SL(term), 10n, 10n, 1n, 0n, y, h1, G.lin_v(SL(term), y, ht))
  +h3 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(G.LIN(10n, 0n, y), G.LIN(11n, 0n, y))) == True{} : Bool}, Nat.add(10n, G.LIN(11n, 0n, y)), G.LIN(11n, 10n, y), G.lin_c(10n, 11n, 0n, y),
    N.le_add_mono_r(G.LIN(11n, 0n, y), 10n, G.LIN(10n, 0n, y), G.lin_x(10n, 0n, 1n, y, N.le_zero_l(SL(bd ++ term)))))
  +h4 = AB.subst(Nat, z => {Nat.is_le(G.LIN(11n, 10n, y), z) == True{} : Bool}, Nat.add(G.LIN(10n, 0n, y), G.LIN(11n, 0n, y)), G.LIN(21n, 0n, y), G.lin_sum(10n, 0n, 11n, 0n, y), h3)
  N.le_trans(Nat.add(SL(t), SL(term)), G.LIN(11n, 10n, y), LC(bd ++ term), h2, h4)

def pl.k(strict: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +w: Nat, +c0: B.Code, +bd: String, +term: String, +at: B.At, +ip: Nat) ->
  POST(R.problem_line(strict, RS(n, h, c, e, la, b, k, o, ns), w, c0, B.Line{bd, term}, at, ip), Nat.add(SL(bd ++ term), WSt(b, h, o))):
  match strict:
    case True{}:
      stop_le(n, h, c, e, la, b, k, o, ns, "", B.Stop{c0, Some{at}, None{}}, bd ++ term, N.le_zero_l(BS(b)))
    case False{}:
      ky(n, h, c, e, la, b, k, o, ns, w, ip, ip, at, bd ++ term, [B.Warning{c0, at}], R.bump(k, False{}, False{}, True{}))

def upl(+tx: String, +W: Nat) -> {Nat.is_le(Nat.add(SL(tx), W), Nat.add(LC(tx), W)) == True{} : Bool}:
  N.le_add_mono_r(W, SL(tx), LC(tx), lc_ge(tx))

# One body line: within its allowance LC(line) more than the bytes held.
def bl(r: B.Res, +bd: String, +term: String, hr: Q.JB(bd, r), +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +opts: B.Opts, +at: B.At, +ip: Nat) ->
  POST(R.body_line(r, RS(n, h, c, e, la, b, k, o, ns), opts, B.Line{bd, term}, at, ip), Nat.add(LC(bd ++ term), WSt(b, h, o))):
  match r:
    case B.Res{kind, +k0, +t, +s}:
      match kind:
        case B.Broken{}:
          post_mono(R.stop(RS(n, h, c, e, la, b, k, o, ns), "", B.Stop{B.Malformed{}, Some{at}, None{}}), Nat.add(SL(bd ++ term), WSt(b, h, o)), Nat.add(LC(bd ++ term), WSt(b, h, o)),
            stop_le(n, h, c, e, la, b, k, o, ns, "", B.Stop{B.Malformed{}, Some{at}, None{}}, bd ++ term, N.le_zero_l(BS(b))), upl(bd ++ term, WSt(b, h, o)))
        case B.NoContig{}:
          post_mono(R.stop(RS(n, h, c, e, la, b, k, o, ns), "", B.Stop{B.UnknownChrom{}, Some{at}, None{}}), Nat.add(SL(bd ++ term), WSt(b, h, o)), Nat.add(LC(bd ++ term), WSt(b, h, o)),
            stop_le(n, h, c, e, la, b, k, o, ns, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}}, bd ++ term, N.le_zero_l(BS(b))), upl(bd ++ term, WSt(b, h, o)))
        case B.Problem{+c0}:
          post_mono(R.problem_line(R.Opts.strict(opts), RS(n, h, c, e, la, b, k, o, ns), R.Opts.w(opts), c0, B.Line{bd, term}, at, ip), Nat.add(SL(bd ++ term), WSt(b, h, o)), Nat.add(LC(bd ++ term), WSt(b, h, o)),
            pl.k(R.Opts.strict(opts), n, h, c, e, la, b, k, o, ns, R.Opts.w(opts), c0, bd, term, at, ip), upl(bd ++ term, WSt(b, h, o)))
        case B.Skipped{}:
          post_mono(R.keyed(RS(n, h, c, e, la, b, k, o, ns), R.Opts.w(opts), R.Item{ip, ip, at, bd ++ term}, Nil{}, R.bump(k, False{}, True{}, False{})), Nat.add(SL(bd ++ term), WSt(b, h, o)), Nat.add(LC(bd ++ term), WSt(b, h, o)),
            ky(n, h, c, e, la, b, k, o, ns, R.Opts.w(opts), ip, ip, at, bd ++ term, Nil{}, R.bump(k, False{}, True{}, False{})), upl(bd ++ term, WSt(b, h, o)))
        case B.Normalized{}:
          +k2 = R.bump(k, Bool.not(String.eq(t, bd)), False{}, False{})
          +hl = AB.subst(Nat, z => {Nat.is_le(z, LC(bd ++ term)) == True{} : Bool}, Nat.add(SL(t), SL(term)), SL(t ++ term), Equal.sym(Nat, SL(t ++ term), Nat.add(SL(t), SL(term)), G.slen_app(t, term)),
            lc_n(bd, term, t, hr))
          post_mono(R.keyed(RS(n, h, c, e, la, b, k, o, ns), R.Opts.w(opts), R.Item{k0, ip, at, t ++ term}, R.stale_note(s, at), k2), Nat.add(SL(t ++ term), WSt(b, h, o)), Nat.add(LC(bd ++ term), WSt(b, h, o)),
            ky(n, h, c, e, la, b, k, o, ns, R.Opts.w(opts), k0, ip, at, t ++ term, R.stale_note(s, at), k2), N.le_add_mono_r(WSt(b, h, o), SL(t ++ term), LC(bd ++ term), hl))

# ---------------------------------------------------------------------------
# Header lines
# ---------------------------------------------------------------------------

def ar2(+B0: Nat, +H: Nat, +A: Nat, +TT: Nat, +TX: Nat) ->
  {Nat.add(B0, Nat.add(H, Nat.add(Nat.add(A, TT), TX))) == Nat.add(Nat.add(Nat.add(B0, H), A), Nat.add(TT, TX)) : Nat}:
  Equal.trans(Nat, Nat.add(B0, Nat.add(H, Nat.add(Nat.add(A, TT), TX))), Nat.add(B0, Nat.add(H, Nat.add(A, Nat.add(TT, TX)))), Nat.add(Nat.add(Nat.add(B0, H), A), Nat.add(TT, TX)),
    Equal.cong(Nat, Nat, z => Nat.add(B0, Nat.add(H, z)), Nat.add(Nat.add(A, TT), TX), Nat.add(A, Nat.add(TT, TX)), N.add_assoc(A, TT, TX)),
    Equal.trans(Nat, Nat.add(B0, Nat.add(H, Nat.add(A, Nat.add(TT, TX)))), Nat.add(B0, Nat.add(Nat.add(H, A), Nat.add(TT, TX))), Nat.add(Nat.add(Nat.add(B0, H), A), Nat.add(TT, TX)),
      Equal.cong(Nat, Nat, z => Nat.add(B0, z), Nat.add(H, Nat.add(A, Nat.add(TT, TX))), Nat.add(Nat.add(H, A), Nat.add(TT, TX)), Equal.sym(Nat, Nat.add(Nat.add(H, A), Nat.add(TT, TX)), Nat.add(H, Nat.add(A, Nat.add(TT, TX))), N.add_assoc(H, A, Nat.add(TT, TX)))),
      Equal.trans(Nat, Nat.add(B0, Nat.add(Nat.add(H, A), Nat.add(TT, TX))), Nat.add(Nat.add(B0, Nat.add(H, A)), Nat.add(TT, TX)), Nat.add(Nat.add(Nat.add(B0, H), A), Nat.add(TT, TX)),
        Equal.sym(Nat, Nat.add(Nat.add(B0, Nat.add(H, A)), Nat.add(TT, TX)), Nat.add(B0, Nat.add(Nat.add(H, A), Nat.add(TT, TX))), N.add_assoc(B0, Nat.add(H, A), Nat.add(TT, TX))),
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(TT, TX)), Nat.add(B0, Nat.add(H, A)), Nat.add(Nat.add(B0, H), A), Equal.sym(Nat, Nat.add(Nat.add(B0, H), A), Nat.add(B0, Nat.add(H, A)), N.add_assoc(B0, H, A))))))

def ar3(+B0: Nat, +H: Nat, +TX: Nat, +O: Nat, +A: Nat) ->
  {Nat.add(Nat.add(B0, Nat.add(Nat.add(H, TX), O)), A) == Nat.add(TX, Nat.add(Nat.add(B0, Nat.add(H, O)), A)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(B0, Nat.add(Nat.add(H, TX), O)), A), Nat.add(Nat.add(B0, Nat.add(TX, Nat.add(H, O))), A), Nat.add(TX, Nat.add(Nat.add(B0, Nat.add(H, O)), A)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(B0, z), A), Nat.add(Nat.add(H, TX), O), Nat.add(TX, Nat.add(H, O)),
      Equal.trans(Nat, Nat.add(Nat.add(H, TX), O), Nat.add(Nat.add(TX, H), O), Nat.add(TX, Nat.add(H, O)),
        Equal.cong(Nat, Nat, z => Nat.add(z, O), Nat.add(H, TX), Nat.add(TX, H), N.add_comm(H, TX)), N.add_assoc(TX, H, O))),
    Equal.trans(Nat, Nat.add(Nat.add(B0, Nat.add(TX, Nat.add(H, O))), A), Nat.add(Nat.add(TX, Nat.add(B0, Nat.add(H, O))), A), Nat.add(TX, Nat.add(Nat.add(B0, Nat.add(H, O)), A)),
      Equal.cong(Nat, Nat, z => Nat.add(z, A), Nat.add(B0, Nat.add(TX, Nat.add(H, O))), Nat.add(TX, Nat.add(B0, Nat.add(H, O))), N.add_left_comm(B0, TX, Nat.add(H, O))),
      N.add_assoc(TX, Nat.add(B0, Nat.add(H, O)), A)))

def hl(isc: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>,
  +opts: B.Opts, +bd: String, +term: String, +X: Nat, +hinv: {Nat.is_le(Nat.add(WSt(b, h, o), AD(opts)), X) == True{} : Bool}) ->
  INV(R.head_line(isc, R.RunSt{n, False{}, h, c, e, la, b, k, o, ns, False{}}, opts, B.Line{bd, term}), Nat.add(LC(bd ++ term), X), AD(opts)):
  match isc:
    case True{}:
      +A = AD(opts)
      +T0 = SL(term)
      +TT = Nat.add(T0, T0)
      +tx = bd ++ term
      +ad = R.added(opts, term)
      +y = {1n+SL(tx) : Nat}
      +eN = Equal.trans(Nat, SL(h ++ (ad ++ tx)), Nat.add(SL(h), SL(ad ++ tx)), Nat.add(SL(h), Nat.add(SL(ad), SL(tx))), G.slen_app(h, ad ++ tx),
        Equal.cong(Nat, Nat, z => Nat.add(SL(h), z), SL(ad ++ tx), Nat.add(SL(ad), SL(tx)), G.slen_app(ad, tx)))
      +h1 = AB.subst(Nat, z => {Nat.is_le(Nat.add(BS(b), z), Nat.add(BS(b), Nat.add(SL(h), Nat.add(Nat.add(A, TT), SL(tx))))) == True{} : Bool}, Nat.add(SL(h), Nat.add(SL(ad), SL(tx))), SL(h ++ (ad ++ tx)),
        Equal.sym(Nat, SL(h ++ (ad ++ tx)), Nat.add(SL(h), Nat.add(SL(ad), SL(tx))), eN),
        N.le_add_mono_l(BS(b), Nat.add(SL(h), Nat.add(SL(ad), SL(tx))), Nat.add(SL(h), Nat.add(Nat.add(A, TT), SL(tx))),
          N.le_add_mono_l(SL(h), Nat.add(SL(ad), SL(tx)), Nat.add(Nat.add(A, TT), SL(tx)), N.le_add_mono_r(SL(tx), SL(ad), Nat.add(A, TT), ad_len(opts, term)))))
      +h2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(BS(b), SL(h ++ (ad ++ tx))), z) == True{} : Bool}, Nat.add(BS(b), Nat.add(SL(h), Nat.add(Nat.add(A, TT), SL(tx)))),
        Nat.add(Nat.add(Nat.add(BS(b), SL(h)), A), Nat.add(TT, SL(tx))), ar2(BS(b), SL(h), A, TT, SL(tx)), h1)
      +h3 = N.le_add_mono_r(A, Nat.add(BS(b), SL(h)), WSt(b, h, o), N.le_add_mono_l(BS(b), SL(h), Nat.add(SL(h), SL(o)), N.le_add_r(SL(h), SL(o))))
      +h4 = N.le_trans(Nat.add(Nat.add(BS(b), SL(h)), A), Nat.add(WSt(b, h, o), A), X, h3, hinv)
      +eT = G.slen_app(bd, term)
      +hT = N.le_trans(T0, SL(tx), y,
        AB.subst(Nat, z => {Nat.is_le(T0, z) == True{} : Bool}, Nat.add(SL(bd), T0), SL(tx), Equal.sym(Nat, SL(tx), Nat.add(SL(bd), T0), eT), N.le_add_l(T0, SL(bd))), N.le_add_l(SL(tx), 1n))
      +h5 = G.lin_add(TT, SL(tx), 2n, 0n, 1n, 0n, y, G.lin_add(T0, T0, 1n, 0n, 1n, 0n, y, G.lin_v(T0, y, hT), G.lin_v(T0, y, hT)), G.lin_v(SL(tx), y, N.le_add_l(SL(tx), 1n)))
      +h6 = N.le_trans(Nat.add(TT, SL(tx)), G.LIN(3n, 0n, y), LC(tx), h5, G.lin_mono(3n, 0n, 21n, 0n, y, {==}, {==}))
      +h7 = N.le_trans(Nat.add(BS(b), SL(h ++ (ad ++ tx))), Nat.add(Nat.add(Nat.add(BS(b), SL(h)), A), Nat.add(TT, SL(tx))), Nat.add(X, LC(tx)), h2, P.le_add(Nat.add(Nat.add(BS(b), SL(h)), A), X, Nat.add(TT, SL(tx)), LC(tx), h4, h6))
      AB.subst(Nat, z => {Nat.is_le(Nat.add(BS(b), SL(h ++ (ad ++ tx))), z) == True{} : Bool}, Nat.add(X, LC(tx)), Nat.add(LC(tx), X), N.add_comm(X, LC(tx)), h7)
    case False{}:
      +tx = bd ++ term
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(BS(b), Nat.add(z, SL(o))), AD(opts)), SL(h ++ tx), Nat.add(SL(h), SL(tx)), G.slen_app(h, tx))
      AB.subst(Nat, z => {Nat.is_le(z, Nat.add(LC(tx), X)) == True{} : Bool}, Nat.add(SL(tx), Nat.add(WSt(b, h, o), AD(opts))), Nat.add(WSt(b, h ++ tx, o), AD(opts)),
        Equal.sym(Nat, Nat.add(WSt(b, h ++ tx, o), AD(opts)), Nat.add(SL(tx), Nat.add(WSt(b, h, o), AD(opts))),
          Equal.trans(Nat, Nat.add(WSt(b, h ++ tx, o), AD(opts)), Nat.add(Nat.add(BS(b), Nat.add(Nat.add(SL(h), SL(tx)), SL(o))), AD(opts)), Nat.add(SL(tx), Nat.add(WSt(b, h, o), AD(opts))),
            e1, ar3(BS(b), SL(h), SL(tx), SL(o), AD(opts)))),
        P.le_add(SL(tx), LC(tx), Nat.add(WSt(b, h, o), AD(opts)), X, lc_ge(tx), hinv))

# ---------------------------------------------------------------------------
# The whole run
# ---------------------------------------------------------------------------

def lstep.b(+fa: List<&2, B.Contig>, +opts: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  +ns: List<&2, B.Note>, +l: B.Line, +X: Nat, +hinv: {Nat.is_le(WSt(b, h, o), X) == True{} : Bool}) ->
  INV(L.line_step(fa, opts, R.RunSt{n, True{}, h, c, e, la, b, k, o, ns, False{}}, l), Nat.add(LC(B.Line.text(l)), X), AD(opts)):
  match l:
    case B.Line{+bd, +term}:
      +fs = B.Rec.fields(bd)
      post_inv(R.body_line(L.judge(fa, bd), RS(1n+n, h, c, e, la, b, k, o, ns), opts, B.Line{bd, term}, B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)),
        Nat.add(LC(bd ++ term), WSt(b, h, o)), Nat.add(LC(bd ++ term), X), AD(opts),
        bl(L.judge(fa, bd), bd, term, Q.judge_len(fa, bd), 1n+n, h, c, e, la, b, k, o, ns, opts, B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)),
        N.le_add_mono_l(LC(bd ++ term), WSt(b, h, o), X, hinv))

def lstep.h(+fa: List<&2, B.Contig>, +opts: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  +ns: List<&2, B.Note>, +l: B.Line, +X: Nat, +hinv: {Nat.is_le(Nat.add(WSt(b, h, o), AD(opts)), X) == True{} : Bool}) ->
  INV(L.line_step(fa, opts, R.RunSt{n, False{}, h, c, e, la, b, k, o, ns, False{}}, l), Nat.add(LC(B.Line.text(l)), X), AD(opts)):
  match l:
    case B.Line{+bd, +term}:
      hl(R.is_chrom_line(bd), 1n+n, h, c, e, la, b, k, o, ns, opts, bd, term, X, hinv)

def halted_up(+o: String, +X: Nat, +Z: Nat, +h: {Nat.is_le(SL(o), Nat.add(X, X)) == True{} : Bool}) -> {Nat.is_le(SL(o), Nat.add(Nat.add(Z, X), Nat.add(Z, X))) == True{} : Bool}:
  N.le_trans(SL(o), Nat.add(X, X), Nat.add(Nat.add(Z, X), Nat.add(Z, X)), h, P.le_add(X, Nat.add(Z, X), X, Nat.add(Z, X), N.le_add_l(X, Z), N.le_add_l(X, Z)))

# One line keeps the invariant, with LC(line) more allowance.
def lstep(+fa: List<&2, B.Contig>, +opts: B.Opts, st: R.RunSt, +l: B.Line, +X: Nat, hinv: INV(st, X, AD(opts))) ->
  INV(L.line_step(fa, opts, st, l), Nat.add(LC(B.Line.text(l)), X), AD(opts)):
  match st:
    case R.RunSt{+n, i, +h, +c, +e, +la, +b, +k, +o, +ns, x}:
      match i x:
        case True{} True{}:
          halted_up(o, X, LC(B.Line.text(l)), hinv)
        case False{} True{}:
          halted_up(o, X, LC(B.Line.text(l)), hinv)
        case True{} False{}:
          lstep.b(fa, opts, n, h, c, e, la, b, k, o, ns, l, X, hinv)
        case False{} False{}:
          lstep.h(fa, opts, n, h, c, e, la, b, k, o, ns, l, X, hinv)

def AC(ls: List<&2, B.Line>, +X: Nat) -> Nat:
  match ls:
    case Nil{}:
      X
    case l <> t:
      AC(t, Nat.add(LC(B.Line.text(l)), X))

def rg(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +opts: B.Opts, +st: R.RunSt, +X: Nat, hinv: INV(st, X, AD(opts))) ->
  INV(L.run.go(ls, fa, opts, st), AC(ls, X), AD(opts)):
  match ls:
    case Nil{}:
      hinv
    case +l <> t:
      rg(t, fa, opts, L.line_step(fa, opts, st, l), Nat.add(LC(B.Line.text(l)), X), lstep(fa, opts, st, l, X, hinv))

def ff(f: R.Flush, +o: String, +ns: List<&2, B.Note>, k: R.Cnt) -> {SL(R.Report.out(R.finish.flush(f, o, ns, k))) == Nat.add(SL(o), SL(FO(f))) : Nat}:
  match f k:
    case R.Broke{+o2, bad, prev} _:
      G.slen_app(o, o2)
    case R.Flushed{+o2, l2} R.Cnt{a, b, c, d}:
      G.slen_app(o, o2)

def fin(st: R.RunSt, +X: Nat, +A: Nat, hinv: INV(st, X, A)) -> {Nat.is_le(SL(R.Report.out(R.finish(st))), Nat.add(X, X)) == True{} : Bool}:
  match st:
    case R.RunSt{n, i, +h, c, e, +l, +b, +k, +o, +ns, x}:
      match i x:
        case True{} True{}:
          hinv
        case False{} True{}:
          hinv
        case False{} False{}:
          N.le_zero_l(Nat.add(X, X))
        case True{} False{}:
          +F = R.flush(b, l)
          +h1 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(BS(b), Nat.add(SL(h), SL(o)))) == True{} : Bool}, Nat.add(SL(FO(F)), SL(o)), Nat.add(SL(o), SL(FO(F))), N.add_comm(SL(FO(F)), SL(o)),
            P.le_add(SL(FO(F)), BS(b), SL(o), Nat.add(SL(h), SL(o)), fl_le(b, l), N.le_add_l(SL(o), SL(h))))
          AB.subst(Nat, z => {Nat.is_le(z, Nat.add(X, X)) == True{} : Bool}, Nat.add(SL(o), SL(FO(F))), SL(R.Report.out(R.finish.flush(F, o, ns, k))), Equal.sym(Nat, SL(R.Report.out(R.finish.flush(F, o, ns, k))), Nat.add(SL(o), SL(FO(F))), ff(F, o, ns, k)),
            N.le_trans(Nat.add(SL(o), SL(FO(F))), X, Nat.add(X, X), N.le_trans(Nat.add(SL(o), SL(FO(F))), WSt(b, h, o), X, h1, hinv), N.le_add_r(X, X)))

def lin_mul(+k: Nat, +y: Nat) -> {G.LIN(k, 0n, y) == Nat.mul(k, y) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(Nat, Nat, z => Nat.add(y, z), G.LIN(j, 0n, y), Nat.mul(j, y), lin_mul(j, y))

def ac_le(ls: List<&2, B.Line>, +X: Nat) -> {Nat.is_le(AC(ls, X), Nat.add(Nat.mul(21n, LT(ls)), X)) == True{} : Bool}:
  match ls:
    case Nil{}:
      N.le_refl(X)
    case +l <> +t:
      +C0 = LC(B.Line.text(l))
      +M = Nat.mul(21n, LT(t))
      +Y1 = {1n+SL(B.Line.text(l)) : Nat}
      +e1 = Equal.trans(Nat, Nat.add(M, Nat.add(C0, X)), Nat.add(Nat.add(C0, M), X), Nat.add(Nat.mul(21n, Nat.add(Y1, LT(t))), X),
        Equal.trans(Nat, Nat.add(M, Nat.add(C0, X)), Nat.add(C0, Nat.add(M, X)), Nat.add(Nat.add(C0, M), X), N.add_left_comm(M, C0, X),
          Equal.sym(Nat, Nat.add(Nat.add(C0, M), X), Nat.add(C0, Nat.add(M, X)), N.add_assoc(C0, M, X))),
        Equal.cong(Nat, Nat, z => Nat.add(z, X), Nat.add(C0, M), Nat.mul(21n, Nat.add(Y1, LT(t))),
          Equal.trans(Nat, Nat.add(C0, M), Nat.add(Nat.mul(21n, Y1), M), Nat.mul(21n, Nat.add(Y1, LT(t))),
            Equal.cong(Nat, Nat, z => Nat.add(z, M), C0, Nat.mul(21n, Y1), lin_mul(21n, Y1)),
            Equal.sym(Nat, Nat.mul(21n, Nat.add(Y1, LT(t))), Nat.add(Nat.mul(21n, Y1), M), N.mul_add(21n, Y1, LT(t))))))
      AB.subst(Nat, z => {Nat.is_le(AC(t, Nat.add(C0, X)), z) == True{} : Bool}, Nat.add(M, Nat.add(C0, X)), Nat.add(Nat.mul(21n, Nat.add(Y1, LT(t))), X), e1, ac_le(t, Nat.add(C0, X)))

def OB(+vcf: String, +opts: B.Opts) -> Nat:
  Nat.add(Nat.mul(63n, 1n+SL(vcf)), AD(opts))

# The output-length lemma: a run writes at most 2 (63 (|vcf| + 1) + 61 +
# |args text|) bytes.
def out_len(+fasta: String, +vcf: String, +opts: B.Opts) -> {Nat.is_le(SL(R.Report.out(L.run(fasta, vcf, opts))), Nat.add(OB(vcf, opts), OB(vcf, opts))) == True{} : Bool}:
  +ls = B.Text.lines(vcf)
  +fa = B.Fasta.parse(fasta)
  +A = AD(opts)
  +h0 = N.le_refl(A)
  +X = AC(ls, A)
  +h2 = fin(L.run.go(ls, fa, opts, R.start_st()), X, A, rg(ls, fa, opts, R.start_st(), A, h0))
  +h4 = N.le_mul_l(21n, LT(ls), Nat.mul(3n, 1n+SL(vcf)), lines_lt(vcf))
  +h5 = AB.subst(Nat, z => {Nat.is_le(Nat.mul(21n, LT(ls)), z) == True{} : Bool}, Nat.mul(21n, Nat.mul(3n, 1n+SL(vcf))), Nat.mul(63n, 1n+SL(vcf)),
    Equal.sym(Nat, Nat.mul(Nat.mul(21n, 3n), 1n+SL(vcf)), Nat.mul(21n, Nat.mul(3n, 1n+SL(vcf))), N.mul_assoc(21n, 3n, 1n+SL(vcf))), h4)
  +h6 = N.le_trans(X, Nat.add(Nat.mul(21n, LT(ls)), A), OB(vcf, opts), ac_le(ls, A), N.le_add_mono_r(A, Nat.mul(21n, LT(ls)), Nat.mul(63n, 1n+SL(vcf)), h5))
  N.le_trans(SL(R.Report.out(L.run(fasta, vcf, opts))), Nat.add(X, X), Nat.add(OB(vcf, opts), OB(vcf, opts)), h2, P.le_add(X, OB(vcf, opts), X, OB(vcf, opts), h6, h6))
