import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_e_defs.bend as SD
import ./proof_e_seg_defs.bend as G

# Phase E, area "seg": the buffer facts phase 1 needs (S's buffer E in front
# of T's, E ready or not as a whole), and small Nat facts.

# Nat and Bool
# ============

law lt_of_le_false:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == False{} : Bool}
  {Nat.is_lt(b, a) == True{} : Bool}

def lt_of_le_false(a, b, e):
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_lt(b, 0n) == True{} : Bool}, P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{}, Equal.sym(Bool, Nat.is_le(0n, b), True{}, P.le_zero_l(b)), e)))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      lt_of_le_false(ap, bp, e)

law lt_pos:
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(0n, b) == True{} : Bool}

def lt_pos(a, b, h):
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, P.lt_zero(a)), h)))
    case 1n+bp:
      {==}

law le_lt_absurd:
  for +a: Nat
  for +b: Nat
  for h1: {Nat.is_le(a, b) == True{} : Bool}
  for h2: {Nat.is_lt(b, a) == True{} : Bool}
  Empty

def le_lt_absurd(a, b, h1, h2):
  match a b:
    case 0n 0n:
      P.false_ne_true(h2)
    case 0n 1n+bp:
      P.false_ne_true(h2)
    case 1n+ap 0n:
      P.false_ne_true(h1)
    case 1n+ap 1n+bp:
      le_lt_absurd(ap, bp, h1, h2)

law eq0_false:
  for +n: Nat
  for h: {Nat.is_lt(0n, n) == True{} : Bool}
  {Nat.is_eq(n, 0n) == False{} : Bool}

def eq0_false(n, h):
  match n:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, P.false_ne_true(h))
    case 1n+m:
      {==}

law or_l_true:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == True{} : Bool}
  for nb: {b == False{} : Bool}
  {a == True{} : Bool}

def or_l_true(a, b, e, nb):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.false_ne_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, nb), e)))

law max_lt:
  for +x: Nat
  for +y: Nat
  for +m: Nat
  for hx: {Nat.is_lt(x, m) == True{} : Bool}
  for hy: {Nat.is_lt(y, m) == True{} : Bool}
  {Nat.is_lt(Nat.max(x, y), m) == True{} : Bool}

def max_lt(x, y, m, hx, hy):
  match x y:
    case 0n _:
      hy
    case 1n+a 0n:
      hx
    case 1n+a 1n+b:
      match m:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+Nat.max(a, b), 0n) == True{} : Bool}, P.false_ne_true(hx))
        case 1n+mp:
          max_lt(a, b, mp, hx, hy)

law max_inpos_lt:
  for +b: List<&2, R.Item>
  for +a: Nat
  for +m: Nat
  for +hb: {G.all_lt(b, m) == True{} : Bool}
  for +ha: {Nat.is_lt(a, m) == True{} : Bool}
  {Nat.is_lt(SD.max_inpos(b, a), m) == True{} : Bool}

def max_inpos_lt(b, a, m, hb, ha):
  match b:
    case Nil{}:
      ha
    case +x <> +t:
      max_inpos_lt(t, Nat.max(a, R.Item.inpos(x)), m, P.and_true_r(Nat.is_lt(R.Item.inpos(x), m), G.all_lt(t, m), hb),
        max_lt(a, R.Item.inpos(x), m, ha, P.and_true_l(Nat.is_lt(R.Item.inpos(x), m), G.all_lt(t, m), hb)))

def le_mono_false.go(+a: Nat, +b: Nat, +w: Nat, +p: Nat, +v: Bool, ev: {Nat.is_le(Nat.add(b, w), p) == v : Bool},
  hab: {Nat.is_le(a, b) == True{} : Bool}, e: {Nat.is_le(Nat.add(a, w), p) == False{} : Bool}) -> {v == False{} : Bool}:
  match v:
    case True{}:
      +t = Q.le_trans(Nat.add(a, w), Nat.add(b, w), p, P.le_add(a, b, w, w, hab, P.le_refl(w)), ev)
      Empty.absurd({True{} == False{} : Bool}, P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(Nat.add(a, w), p), False{}, Equal.sym(Bool, Nat.is_le(Nat.add(a, w), p), True{}, t), e)))
    case False{}:
      {==}

law le_mono_false:
  for +a: Nat
  for +b: Nat
  for +w: Nat
  for +p: Nat
  for hab: {Nat.is_le(a, b) == True{} : Bool}
  for e: {Nat.is_le(Nat.add(a, w), p) == False{} : Bool}
  {Nat.is_le(Nat.add(b, w), p) == False{} : Bool}

def le_mono_false(a, b, w, p, hab, e):
  le_mono_false.go(a, b, w, p, Nat.is_le(Nat.add(b, w), p), {==}, hab, e)

# Maybe and the last item
# =======================

law or_some:
  for +a: Maybe<&2, R.Item>
  for +x: R.Item
  for +m: Maybe<&2, R.Item>
  {Maybe.or(&2, R.Item, Maybe.or(&2, R.Item, a, Some{x}), m) == Maybe.or(&2, R.Item, a, Some{x}) : Maybe<&2, R.Item>}

def or_some(a, x, m):
  match a:
    case None{}:
      {==}
    case Some{+y}:
      {==}

law flast_or:
  for +xs: List<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  {S.flast(xs, q) == Maybe.or(&2, R.Item, SD.last_item(xs), q) : Maybe<&2, R.Item>}

def flast_or(xs, q):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Maybe<&2, R.Item>, S.flast(t, Some{x}), Maybe.or(&2, R.Item, SD.last_item(t), Some{x}), flast_or(t, Some{x})) :
        {_ == Maybe.or(&2, R.Item, Maybe.or(&2, R.Item, SD.last_item(t), Some{x}), q) : Maybe<&2, R.Item>}
      Equal.sym(Maybe<&2, R.Item>, Maybe.or(&2, R.Item, Maybe.or(&2, R.Item, SD.last_item(t), Some{x}), q), Maybe.or(&2, R.Item, SD.last_item(t), Some{x}),
        or_some(SD.last_item(t), x, q))

law last_or_ne:
  for +xs: List<&2, R.Item>
  for +m: Maybe<&2, R.Item>
  for h: {List.is_empty(&2, R.Item, xs) == False{} : Bool}
  {Maybe.or(&2, R.Item, SD.last_item(xs), m) == SD.last_item(xs) : Maybe<&2, R.Item>}

def last_or_ne(xs, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Maybe.or(&2, R.Item, None{}, m) == None{} : Maybe<&2, R.Item>}, P.true_ne_false(h))
    case +x <> +t:
      or_some(SD.last_item(t), x, m)

law last_app_ne:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h: {List.is_empty(&2, R.Item, ys) == False{} : Bool}
  {SD.last_item(S.app(xs, ys)) == SD.last_item(ys) : Maybe<&2, R.Item>}

def last_app_ne(xs, ys, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Maybe<&2, R.Item>, SD.last_item(S.app(t, ys)), SD.last_item(ys), last_app_ne(t, ys, h)) :
        {Maybe.or(&2, R.Item, _, Some{x}) == SD.last_item(ys) : Maybe<&2, R.Item>}
      last_or_ne(ys, Some{x}, h)

# The buffer
# ==========

def ins_front.go(+it: R.Item, +x: R.Item, +t: List<&2, R.Item>, +l: Nat, +v: Bool,
  ev: {Nat.is_le(R.Item.key(x), R.Item.key(it)) == v : Bool},
  hx: {Nat.is_le(l, R.Item.key(x)) == True{} : Bool}, hk: {Nat.is_le(l, R.Item.key(it)) == False{} : Bool}) ->
  {R.insert.put(v, x, it, t, R.insert(it, t)) == it <> x <> t : List<&2, R.Item>}:
  match v:
    case True{}:
      +lk = Q.le_trans(l, R.Item.key(x), R.Item.key(it), hx, ev)
      Empty.absurd({x <> R.insert(it, t) == it <> x <> t : List<&2, R.Item>},
        P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(l, R.Item.key(it)), False{}, Equal.sym(Bool, Nat.is_le(l, R.Item.key(it)), True{}, lk), hk)))
    case False{}:
      {==}

# An item below every key of the buffer goes first.
law ins_front:
  for +it: R.Item
  for +b: List<&2, R.Item>
  for +l: Nat
  for +hb: {SD.keys_ge(b, l) == True{} : Bool}
  for +hk: {Nat.is_le(l, R.Item.key(it)) == False{} : Bool}
  {R.insert(it, b) == it <> b : List<&2, R.Item>}

def ins_front(it, b, l, hb, hk):
  match b:
    case Nil{}:
      {==}
    case +x <> +t:
      ins_front.go(it, x, t, l, Nat.is_le(R.Item.key(x), R.Item.key(it)), {==},
        P.and_true_l(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(t, l), hb), hk)

law tr_app_ready:
  for +w: Nat
  for +p: Nat
  for +e: List<&2, R.Item>
  for +c: List<&2, R.Item>
  for +h: {S.all_ready(e, w, p) == True{} : Bool}
  {R.take_ready(w, p, S.app(e, c)) == S.app(e, R.take_ready(w, p, c)) : List<&2, R.Item>}

def tr_app_ready(w, p, e, c, h):
  match e:
    case Nil{}:
      {==}
    case +x <> +t:
      +hr = P.and_true_l(R.ready(w, p, x), S.all_ready(t, w, p), h)
      %Equal.sym(Bool, R.ready(w, p, x), True{}, hr) :
        {R.take_ready.go(x <> S.app(t, c), _, w, p) == x <> S.app(t, R.take_ready(w, p, c)) : List<&2, R.Item>}
      %tr_app_ready(w, p, t, c, P.and_true_r(R.ready(w, p, x), S.all_ready(t, w, p), h)) :
        {x <> R.take_ready(w, p, S.app(t, c)) == x <> _ : List<&2, R.Item>}
      {==}

law dr_app_ready:
  for +w: Nat
  for +p: Nat
  for +e: List<&2, R.Item>
  for +c: List<&2, R.Item>
  for +h: {S.all_ready(e, w, p) == True{} : Bool}
  {R.drop_ready(w, p, S.app(e, c)) == R.drop_ready(w, p, c) : List<&2, R.Item>}

def dr_app_ready(w, p, e, c, h):
  match e:
    case Nil{}:
      {==}
    case +x <> +t:
      +hr = P.and_true_l(R.ready(w, p, x), S.all_ready(t, w, p), h)
      %Equal.sym(Bool, R.ready(w, p, x), True{}, hr) :
        {R.drop_ready.go(x <> S.app(t, c), _, w, p) == R.drop_ready(w, p, c) : List<&2, R.Item>}
      dr_app_ready(w, p, t, c, P.and_true_r(R.ready(w, p, x), S.all_ready(t, w, p), h))

def tr_app_nr.go(+w: Nat, +p: Nat, +x: R.Item, +t: List<&2, R.Item>, +c: List<&2, R.Item>, +rx: Bool,
  h: {Bool.and(rx, S.all_ready(t, w, p)) == False{} : Bool},
  ih: {S.all_ready(t, w, p) == False{} : Bool} -> {R.take_ready(w, p, S.app(t, c)) == R.take_ready(w, p, t) : List<&2, R.Item>}) ->
  {R.take_ready.go(x <> S.app(t, c), rx, w, p) == R.take_ready.go(x <> t, rx, w, p) : List<&2, R.Item>}:
  match rx:
    case True{}:
      %ih(h) : {x <> R.take_ready(w, p, S.app(t, c)) == x <> _ : List<&2, R.Item>}
      {==}
    case False{}:
      {==}

# E not all ready: the ready prefix of E ++ C is E's.
law tr_app_nr:
  for +w: Nat
  for +p: Nat
  for +e: List<&2, R.Item>
  for +c: List<&2, R.Item>
  for h: {S.all_ready(e, w, p) == False{} : Bool}
  {R.take_ready(w, p, S.app(e, c)) == R.take_ready(w, p, e) : List<&2, R.Item>}

def tr_app_nr(w, p, e, c, h):
  match e:
    case Nil{}:
      Empty.absurd({R.take_ready(w, p, c) == Nil{} : List<&2, R.Item>}, P.true_ne_false(h))
    case +x <> +t:
      tr_app_nr.go(w, p, x, t, c, R.ready(w, p, x), h, h2 => tr_app_nr(w, p, t, c, h2))

def dr_app_nr.go(+w: Nat, +p: Nat, +x: R.Item, +t: List<&2, R.Item>, +c: List<&2, R.Item>, +rx: Bool,
  h: {Bool.and(rx, S.all_ready(t, w, p)) == False{} : Bool},
  ih: {S.all_ready(t, w, p) == False{} : Bool} -> {R.drop_ready(w, p, S.app(t, c)) == S.app(R.drop_ready(w, p, t), c) : List<&2, R.Item>}) ->
  {R.drop_ready.go(x <> S.app(t, c), rx, w, p) == S.app(R.drop_ready.go(x <> t, rx, w, p), c) : List<&2, R.Item>}:
  match rx:
    case True{}:
      ih(h)
    case False{}:
      {==}

law dr_app_nr:
  for +w: Nat
  for +p: Nat
  for +e: List<&2, R.Item>
  for +c: List<&2, R.Item>
  for h: {S.all_ready(e, w, p) == False{} : Bool}
  {R.drop_ready(w, p, S.app(e, c)) == S.app(R.drop_ready(w, p, e), c) : List<&2, R.Item>}

def dr_app_nr(w, p, e, c, h):
  match e:
    case Nil{}:
      Empty.absurd({R.drop_ready(w, p, c) == c : List<&2, R.Item>}, P.true_ne_false(h))
    case +x <> +t:
      dr_app_nr.go(w, p, x, t, c, R.ready(w, p, x), h, h2 => dr_app_nr(w, p, t, c, h2))

def de_ne.go(+w: Nat, +p: Nat, +x: R.Item, +t: List<&2, R.Item>, +rx: Bool,
  h: {Bool.and(rx, S.all_ready(t, w, p)) == False{} : Bool},
  ih: {S.all_ready(t, w, p) == False{} : Bool} -> {List.is_empty(&2, R.Item, R.drop_ready(w, p, t)) == False{} : Bool}) ->
  {List.is_empty(&2, R.Item, R.drop_ready.go(x <> t, rx, w, p)) == False{} : Bool}:
  match rx:
    case True{}:
      ih(h)
    case False{}:
      {==}

# E not all ready: some of it stays.
law de_ne:
  for +w: Nat
  for +p: Nat
  for +e: List<&2, R.Item>
  for h: {S.all_ready(e, w, p) == False{} : Bool}
  {List.is_empty(&2, R.Item, R.drop_ready(w, p, e)) == False{} : Bool}

def de_ne(w, p, e, h):
  match e:
    case Nil{}:
      Empty.absurd({True{} == False{} : Bool}, P.true_ne_false(h))
    case +x <> +t:
      de_ne.go(w, p, x, t, R.ready(w, p, x), h, h2 => de_ne(w, p, t, h2))

def nr_bound.go(+w: Nat, +p: Nat, +x: R.Item, +t: List<&2, R.Item>, +m: Nat, +rx: Bool,
  erx: {R.ready(w, p, x) == rx : Bool},
  h: {Bool.and(rx, S.all_ready(t, w, p)) == False{} : Bool},
  hx: {Nat.is_le(R.Item.key(x), m) == True{} : Bool},
  ih: {S.all_ready(t, w, p) == False{} : Bool} -> {Nat.is_le(Nat.add(m, w), p) == False{} : Bool}) ->
  {Nat.is_le(Nat.add(m, w), p) == False{} : Bool}:
  match rx:
    case True{}:
      ih(h)
    case False{}:
      le_mono_false(R.Item.key(x), m, w, p, hx, erx)

# E not all ready at p: every key at most m has m + w > p.
law nr_bound:
  for +w: Nat
  for +p: Nat
  for +e: List<&2, R.Item>
  for +m: Nat
  for h: {S.all_ready(e, w, p) == False{} : Bool}
  for +hl: {S.all_le(e, m) == True{} : Bool}
  {Nat.is_le(Nat.add(m, w), p) == False{} : Bool}

def nr_bound(w, p, e, m, h, hl):
  match e:
    case Nil{}:
      Empty.absurd({Nat.is_le(Nat.add(m, w), p) == False{} : Bool}, P.true_ne_false(h))
    case +x <> +t:
      nr_bound.go(w, p, x, t, m, R.ready(w, p, x), {==}, h,
        P.and_true_l(Nat.is_le(R.Item.key(x), m), S.all_le(t, m), hl),
        h2 => nr_bound(w, p, t, m, h2, P.and_true_r(Nat.is_le(R.Item.key(x), m), S.all_le(t, m), hl)))

law hr_false:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  for +m: Nat
  for +l: Nat
  for +e: {Nat.is_le(Nat.add(m, w), p) == False{} : Bool}
  for +hml: {Nat.is_le(m, l) == True{} : Bool}
  for +hk: {SD.keys_ge(b, l) == True{} : Bool}
  {R.head_ready(w, p, b) == False{} : Bool}

def hr_false(w, p, b, m, l, e, hml, hk):
  match b:
    case Nil{}:
      {==}
    case +y <> +t:
      le_mono_false(m, R.Item.key(y), w, p, Q.le_trans(m, l, R.Item.key(y), hml, P.and_true_l(Nat.is_le(l, R.Item.key(y)), SD.keys_ge(t, l), hk)), e)

law tr_nil:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  for e: {R.head_ready(w, p, b) == False{} : Bool}
  {R.take_ready(w, p, b) == Nil{} : List<&2, R.Item>}

def tr_nil(w, p, b, e):
  match b:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(Bool, R.ready(w, p, y), False{}, e) : {R.take_ready.go(y <> t, _, w, p) == Nil{} : List<&2, R.Item>}
      {==}

law dr_self:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  for e: {R.head_ready(w, p, b) == False{} : Bool}
  {R.drop_ready(w, p, b) == b : List<&2, R.Item>}

def dr_self(w, p, b, e):
  match b:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(Bool, R.ready(w, p, y), False{}, e) : {R.drop_ready.go(y <> t, _, w, p) == y <> t : List<&2, R.Item>}
      {==}

law all_le_r:
  for +a: List<&2, R.Item>
  for +b: List<&2, R.Item>
  for +m: Nat
  for +h: {S.all_le(S.app(a, b), m) == True{} : Bool}
  {S.all_le(b, m) == True{} : Bool}

def all_le_r(a, b, m, h):
  match a:
    case Nil{}:
      h
    case +x <> +t:
      all_le_r(t, b, m, P.and_true_r(Nat.is_le(R.Item.key(x), m), S.all_le(S.app(t, b), m), h))

law pre_nil:
  for +f: R.Flush
  {R.Flush.pre("", f) == f : R.Flush}

def pre_nil(f):
  match f:
    case R.Flushed{o, l}:
      {==}
    case R.Broke{o, b, p}:
      {==}

law pre_pre:
  for +a: String
  for +b: String
  for +f: R.Flush
  {R.Flush.pre(a, R.Flush.pre(b, f)) == R.Flush.pre(a ++ b, f) : R.Flush}

def pre_pre(a, b, f):
  match f:
    case R.Flushed{+o, l}:
      %Q.s_append_assoc(a, b, o) : {R.Flushed{_, l} == R.Flushed{(a ++ b) ++ o, l} : R.Flush}
      {==}
    case R.Broke{+o, bd, p}:
      %Q.s_append_assoc(a, b, o) : {R.Broke{_, bd, p} == R.Broke{(a ++ b) ++ o, bd, p} : R.Flush}
      {==}

# A sorted E in front: written whole, then C from E's last.
law flush_app:
  for +e: List<&2, R.Item>
  for +c: List<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +s: {S.sorted_from(e, S.lkey(q)) == True{} : Bool}
  {R.flush(S.app(e, c), q) == R.Flush.pre(L.texts(e), R.flush(c, S.flast(e, q))) : R.Flush}

def flush_app(e, c, q, s):
  match e:
    case Nil{}:
      Equal.sym(R.Flush, R.Flush.pre("", R.flush(c, q)), R.flush(c, q), pre_nil(R.flush(c, q)))
    case +x <> +t:
      +ok = P.and_true_l(Nat.is_le(S.lkey(q), R.Item.key(x)), S.sorted_from(t, R.Item.key(x)), s)
      +ok2 = Equal.trans(Bool, R.flush.ok(q, R.Item.key(x)), Nat.is_le(S.lkey(q), R.Item.key(x)), True{}, S.ok_lkey(q, R.Item.key(x)), ok)
      %Equal.sym(Bool, R.flush.ok(q, R.Item.key(x)), True{}, ok2) :
        {R.flush.put(_, x, q, R.flush(S.app(t, c), Some{x})) == R.Flush.pre(R.Item.text(x) ++ L.texts(t), R.flush(c, S.flast(t, Some{x}))) : R.Flush}
      %Equal.sym(R.Flush, R.flush(S.app(t, c), Some{x}), R.Flush.pre(L.texts(t), R.flush(c, S.flast(t, Some{x}))),
        flush_app(t, c, Some{x}, P.and_true_r(Nat.is_le(S.lkey(q), R.Item.key(x)), S.sorted_from(t, R.Item.key(x)), s))) :
        {R.Flush.pre(R.Item.text(x), _) == R.Flush.pre(R.Item.text(x) ++ L.texts(t), R.flush(c, S.flast(t, Some{x}))) : R.Flush}
      pre_pre(R.Item.text(x), L.texts(t), R.flush(c, S.flast(t, Some{x})))

def gnb.go(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mb: Nat, +n: Nat, +i: Bool, +hh: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +tl: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +x: Bool,
  h: {G.Good1(c0, se, sc, l, mb, R.RunSt{n, i, hh, c, e, tl, b, k, o, ns, x}) == True{} : Bool}) ->
  {G.Bad(l, R.RunSt{n, i, hh, c, e, tl, b, k, o, ns, x}) == False{} : Bool}:
  match e x:
    case _ True{}:
      Empty.absurd({G.Bad(l, R.RunSt{n, i, hh, c, e, tl, b, k, o, ns, True{}}) == False{} : Bool}, P.false_ne_true(h))
    case +y <> +ys False{}:
      {==}
    case Nil{} False{}:
      +gd = G.Good(c0, se, sc, R.RunSt{n, i, hh, c, Nil{}, tl, b, k, o, ns, False{}})
      +g1 = P.and_true_r(gd, G.G1(l, mb, R.RunSt{n, i, hh, c, Nil{}, tl, b, k, o, ns, False{}}), h)
      +kb = SD.keys_ge(b, l) && Nat.is_le(mb, SD.max_inpos(b, SD.real_inpos(tl)))
      +g2 = P.and_true_r(Nat.is_lt(0n, n), kb, g1)
      +kg = P.and_true_l(SD.keys_ge(b, l), Nat.is_le(mb, SD.max_inpos(b, SD.real_inpos(tl))), g2)
      %Equal.sym(Bool, SD.keys_ge(b, l), True{}, kg) : {Bool.not(_) == False{} : Bool}
      {==}

law good1_notbad:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +l: Nat
  for +mb: Nat
  for +st: R.RunSt
  for h: {G.Good1(c0, se, sc, l, mb, st) == True{} : Bool}
  {G.Bad(l, st) == False{} : Bool}

def good1_notbad(c0, se, sc, l, mb, st, h):
  match st:
    case R.RunSt{+n, +i, +hh, +c, +e, +tl, +b, +k, +o, +ns, +x}:
      gnb.go(c0, se, sc, l, mb, n, i, hh, c, e, tl, b, k, o, ns, x, h)
