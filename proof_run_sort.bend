import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q

# Lemmas about the buffer of run.bend (insert, take_ready, drop_ready, flush)
# and the spec's sort (L.isort, L.texts).

def key(x: R.Item) -> Nat:
  R.Item.key(x)

# The key of the last item written (0 before any).
def lkey(m: Maybe<&2, R.Item>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      R.Item.key(x)

# Every key is at most k.
def all_le(xs: List<&2, R.Item>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_le(R.Item.key(x), k) && all_le(t, k)

# Keys never go down, starting from k.
def sorted_from(xs: List<&2, R.Item>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Nat.is_le(k, R.Item.key(x)) && sorted_from(t, R.Item.key(x))

# Some key is below k.
def any_below(xs: List<&2, R.Item>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Nat.is_le(1n+R.Item.key(x), k) || any_below(t, k)

# The last item written by a flush that does not break.
def flast(xs: List<&2, R.Item>, last: Maybe<&2, R.Item>) -> Maybe<&2, R.Item>:
  match xs:
    case Nil{}:
      last
    case x <> t:
      flast(t, Some{x})

def app(xs: List<&2, R.Item>, ys: List<&2, R.Item>) -> List<&2, R.Item>:
  List.append(&2, R.Item, xs, ys)

# Bool
# ====

law or_true_r:
  for +a: Bool
  {Bool.or(a, True{}) == True{} : Bool}

def or_true_r(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law or_true_l:
  for +a: Bool
  for +b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_true_l(a, b, e):
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

law or_true_rr:
  for +a: Bool
  for +b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_true_rr(a, b, e):
  %Equal.sym(Bool, b, True{}, e) : {Bool.or(a, _) == True{} : Bool}
  or_true_r(a)

law and_intro:
  for +a: Bool
  for +b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_intro(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

law or_false_intro:
  for +a: Bool
  for +b: Bool
  for ea: {a == False{} : Bool}
  for eb: {b == False{} : Bool}
  {Bool.or(a, b) == False{} : Bool}

def or_false_intro(a, b, ea, eb):
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

law or_cases_r:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == True{} : Bool}
  for na: {a == False{} : Bool}
  {b == True{} : Bool}

def or_cases_r(a, b, e, na):
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == True{} : Bool}, P.true_ne_false(na))

law broke_ne_flushed:
  for -o: String
  for -b: B.At
  for -p: Maybe<&2, B.At>
  for -o2: String
  for -l2: Maybe<&2, R.Item>
  for e: {R.Broke{o, b, p} == R.Flushed{o2, l2} : R.Flush}
  Empty

def Flush.disc(f: R.Flush) -> Type:
  match f:
    case R.Flushed{o, l}:
      Unit
    case R.Broke{o, b, p}:
      Empty

def broke_ne_flushed(o, b, p, o2, l2, e):
  %Equal.sym(R.Flush, R.Broke{o, b, p}, R.Flushed{o2, l2}, e) : Flush.disc(_)
  Unit{}

# Nat
# ===

law not_s_le:
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_le(b, a) == True{} : Bool}
  {Nat.is_le(1n+a, b) == False{} : Bool}

def not_s_le.go(+a: Nat, +b: Nat, +c: Bool, ec: {Nat.is_le(1n+a, b) == c : Bool}, h: {Nat.is_le(b, a) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Q.le_s_not(a, b, ec, h))

def not_s_le(a, b, h):
  not_s_le.go(a, b, Nat.is_le(1n+a, b), {==}, h)

# Flush
# =====

# flush.ok is the test lkey(last) <= k.
law ok_lkey:
  for +last: Maybe<&2, R.Item>
  for +k: Nat
  {R.flush.ok(last, k) == Nat.is_le(lkey(last), k) : Bool}

def ok_lkey(last, k):
  match last:
    case None{}:
      Equal.sym(Bool, Nat.is_le(0n, k), True{}, P.le_zero_l(k))
    case Some{x}:
      {==}

# A flush of sorted items writes them all.
law flush_sorted:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for +s: {sorted_from(xs, lkey(last)) == True{} : Bool}
  {R.flush(xs, last) == R.Flushed{L.texts(xs), flast(xs, last)} : R.Flush}

def flush_sorted(xs, last, s):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +ok = P.and_true_l(Nat.is_le(lkey(last), R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      +st = P.and_true_r(Nat.is_le(lkey(last), R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      +ok2 = Equal.trans(Bool, R.flush.ok(last, R.Item.key(x)), Nat.is_le(lkey(last), R.Item.key(x)), True{}, ok_lkey(last, R.Item.key(x)), ok)
      %Equal.sym(Bool, R.flush.ok(last, R.Item.key(x)), True{}, ok2) :
        {R.flush.put(_, x, last, R.flush(t, Some{x})) == R.Flushed{R.Item.text(x) ++ L.texts(t), flast(t, Some{x})} : R.Flush}
      %Equal.sym(R.Flush, R.flush(t, Some{x}), R.Flushed{L.texts(t), flast(t, Some{x})}, flush_sorted(t, Some{x}, st)) :
        {R.Flush.pre(R.Item.text(x), _) == R.Flushed{R.Item.text(x) ++ L.texts(t), flast(t, Some{x})} : R.Flush}
      {==}

def flush_ok_sorted.go(+x: R.Item, +t: List<&2, R.Item>, +last: Maybe<&2, R.Item>, -o2: String, -l2: Maybe<&2, R.Item>,
  +c: Bool, f: R.Flush, ec: {R.flush.ok(last, R.Item.key(x)) == c : Bool}, ef: {R.flush(t, Some{x}) == f : R.Flush},
  e: {R.flush.put(c, x, last, f) == R.Flushed{o2, l2} : R.Flush},
  ih: @o: String -> @l: Maybe<&2, R.Item> -> {R.flush(t, Some{x}) == R.Flushed{o, l} : R.Flush} -> {sorted_from(t, R.Item.key(x)) == True{} : Bool}) ->
  {sorted_from(x <> t, lkey(last)) == True{} : Bool}:
  match c f:
    case False{} _:
      Empty.absurd({sorted_from(x <> t, lkey(last)) == True{} : Bool},
        broke_ne_flushed("", R.Item.at(x), R.at_of(last), o2, l2, e))
    case True{} R.Broke{o, b, p}:
      Empty.absurd({sorted_from(x <> t, lkey(last)) == True{} : Bool},
        broke_ne_flushed(R.Item.text(x) ++ o, b, p, o2, l2, e))
    case True{} R.Flushed{o, l}:
      and_intro(Nat.is_le(lkey(last), R.Item.key(x)), sorted_from(t, R.Item.key(x)),
        Equal.trans(Bool, Nat.is_le(lkey(last), R.Item.key(x)), R.flush.ok(last, R.Item.key(x)), True{},
          Equal.sym(Bool, R.flush.ok(last, R.Item.key(x)), Nat.is_le(lkey(last), R.Item.key(x)), ok_lkey(last, R.Item.key(x))), ec),
        ih(o, l, ef))

# A flush that does not break had sorted items.
law flush_ok_sorted:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for -o2: String
  for -l2: Maybe<&2, R.Item>
  for e: {R.flush(xs, last) == R.Flushed{o2, l2} : R.Flush}
  {sorted_from(xs, lkey(last)) == True{} : Bool}

def flush_ok_sorted(xs, last, o2, l2, e):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      flush_ok_sorted.go(x, t, last, o2, l2, R.flush.ok(last, R.Item.key(x)), R.flush(t, Some{x}), {==}, {==}, e,
        o => l => ef => flush_ok_sorted(t, Some{x}, o, l, ef))

# Sorted lists
# ============

law sorted_rest:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for +s: {sorted_from(app(xs, ys), lkey(last)) == True{} : Bool}
  {sorted_from(ys, lkey(flast(xs, last))) == True{} : Bool}

def sorted_rest(xs, ys, last, s):
  match xs:
    case Nil{}:
      s
    case +x <> +t:
      sorted_rest(t, ys, Some{x}, P.and_true_r(Nat.is_le(lkey(last), R.Item.key(x)), sorted_from(app(t, ys), R.Item.key(x)), s))

law sorted_prefix:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +k: Nat
  for +s: {sorted_from(app(xs, ys), k) == True{} : Bool}
  {sorted_from(xs, k) == True{} : Bool}

def sorted_prefix(xs, ys, k, s):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      and_intro(Nat.is_le(k, R.Item.key(x)), sorted_from(t, R.Item.key(x)),
        P.and_true_l(Nat.is_le(k, R.Item.key(x)), sorted_from(app(t, ys), R.Item.key(x)), s),
        sorted_prefix(t, ys, R.Item.key(x), P.and_true_r(Nat.is_le(k, R.Item.key(x)), sorted_from(app(t, ys), R.Item.key(x)), s)))

law lkey_mono:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for +s: {sorted_from(xs, lkey(last)) == True{} : Bool}
  {Nat.is_le(lkey(last), lkey(flast(xs, last))) == True{} : Bool}

def lkey_mono(xs, last, s):
  match xs:
    case Nil{}:
      P.le_refl(lkey(last))
    case +x <> +t:
      Q.le_trans(lkey(last), R.Item.key(x), lkey(flast(t, Some{x})),
        P.and_true_l(Nat.is_le(lkey(last), R.Item.key(x)), sorted_from(t, R.Item.key(x)), s),
        lkey_mono(t, Some{x}, P.and_true_r(Nat.is_le(lkey(last), R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)))

law all_le_flast:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for +s: {sorted_from(xs, lkey(last)) == True{} : Bool}
  {all_le(xs, lkey(flast(xs, last))) == True{} : Bool}

def all_le_flast(xs, last, s):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +st = P.and_true_r(Nat.is_le(lkey(last), R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      and_intro(Nat.is_le(R.Item.key(x), lkey(flast(t, Some{x}))), all_le(t, lkey(flast(t, Some{x}))),
        lkey_mono(t, Some{x}, st), all_le_flast(t, Some{x}, st))

law all_le_mono:
  for +xs: List<&2, R.Item>
  for +a: Nat
  for +b: Nat
  for +h: {all_le(xs, a) == True{} : Bool}
  for +ab: {Nat.is_le(a, b) == True{} : Bool}
  {all_le(xs, b) == True{} : Bool}

def all_le_mono(xs, a, b, h, ab):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      and_intro(Nat.is_le(R.Item.key(x), b), all_le(t, b),
        Q.le_trans(R.Item.key(x), a, b, P.and_true_l(Nat.is_le(R.Item.key(x), a), all_le(t, a), h), ab),
        all_le_mono(t, a, b, P.and_true_r(Nat.is_le(R.Item.key(x), a), all_le(t, a), h), ab))

law all_le_app:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +k: Nat
  for +h1: {all_le(xs, k) == True{} : Bool}
  for +h2: {all_le(ys, k) == True{} : Bool}
  {all_le(app(xs, ys), k) == True{} : Bool}

def all_le_app(xs, ys, k, h1, h2):
  match xs:
    case Nil{}:
      h2
    case +x <> +t:
      and_intro(Nat.is_le(R.Item.key(x), k), all_le(app(t, ys), k),
        P.and_true_l(Nat.is_le(R.Item.key(x), k), all_le(t, k), h1),
        all_le_app(t, ys, k, P.and_true_r(Nat.is_le(R.Item.key(x), k), all_le(t, k), h1), h2))

# The buffer
# ==========

def take_drop.go(+w: Nat, +p: Nat, +x: R.Item, +t: List<&2, R.Item>, +r: Bool,
  ih: {app(R.take_ready(w, p, t), R.drop_ready(w, p, t)) == t : List<&2, R.Item>}) ->
  {app(R.take_ready.go(x <> t, r, w, p), R.drop_ready.go(x <> t, r, w, p)) == x <> t : List<&2, R.Item>}:
  match r:
    case True{}:
      %ih : {x <> app(R.take_ready(w, p, t), R.drop_ready(w, p, t)) == x <> _ : List<&2, R.Item>}
      {==}
    case False{}:
      {==}

law take_drop:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  {app(R.take_ready(w, p, b), R.drop_ready(w, p, b)) == b : List<&2, R.Item>}

def take_drop(w, p, b):
  match b:
    case Nil{}:
      {==}
    case +x <> +t:
      take_drop.go(w, p, x, t, R.ready(w, p, x), take_drop(w, p, t))

def insert_sorted.go(+e: R.Item, +x: R.Item, +t: List<&2, R.Item>, +k: Nat, +c: Bool,
  ec: {Nat.is_le(R.Item.key(x), R.Item.key(e)) == c : Bool},
  kx: {Nat.is_le(k, R.Item.key(x)) == True{} : Bool}, st: {sorted_from(t, R.Item.key(x)) == True{} : Bool},
  ke: {Nat.is_le(k, R.Item.key(e)) == True{} : Bool},
  ih: {Nat.is_le(R.Item.key(x), R.Item.key(e)) == True{} : Bool} -> {sorted_from(R.insert(e, t), R.Item.key(x)) == True{} : Bool}) ->
  {sorted_from(R.insert.put(c, x, e, t, R.insert(e, t)), k) == True{} : Bool}:
  match c:
    case True{}:
      and_intro(Nat.is_le(k, R.Item.key(x)), sorted_from(R.insert(e, t), R.Item.key(x)), kx, ih(ec))
    case False{}:
      and_intro(Nat.is_le(k, R.Item.key(e)), sorted_from(x <> t, R.Item.key(e)), ke,
        and_intro(Nat.is_le(R.Item.key(e), R.Item.key(x)), sorted_from(t, R.Item.key(x)),
          Q.le_flip(R.Item.key(x), R.Item.key(e), ec), st))

# Inserting an item no lower than k keeps a list sorted from k.
law insert_sorted:
  for +e: R.Item
  for +b: List<&2, R.Item>
  for +k: Nat
  for +s: {sorted_from(b, k) == True{} : Bool}
  for +ke: {Nat.is_le(k, R.Item.key(e)) == True{} : Bool}
  {sorted_from(R.insert(e, b), k) == True{} : Bool}

def insert_sorted(e, b, k, s, ke):
  match b:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_le(k, R.Item.key(e)), True{}, ke) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case +x <> +t:
      +kx = P.and_true_l(Nat.is_le(k, R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      +st = P.and_true_r(Nat.is_le(k, R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      insert_sorted.go(e, x, t, k, Nat.is_le(R.Item.key(x), R.Item.key(e)), {==}, kx, st, ke,
        h => insert_sorted(e, t, R.Item.key(x), st, h))

# Inserting after items that are all no higher.
law insert_app:
  for +e: R.Item
  for +ws: List<&2, R.Item>
  for +b: List<&2, R.Item>
  for +h: {all_le(ws, R.Item.key(e)) == True{} : Bool}
  {R.insert(e, app(ws, b)) == app(ws, R.insert(e, b)) : List<&2, R.Item>}

def insert_app(e, ws, b, h):
  match ws:
    case Nil{}:
      {==}
    case +w <> +t:
      +h1 = P.and_true_l(Nat.is_le(R.Item.key(w), R.Item.key(e)), all_le(t, R.Item.key(e)), h)
      +h2 = P.and_true_r(Nat.is_le(R.Item.key(w), R.Item.key(e)), all_le(t, R.Item.key(e)), h)
      %Equal.sym(Bool, Nat.is_le(R.Item.key(w), R.Item.key(e)), True{}, h1) :
        {R.insert.put(_, w, e, app(t, b), R.insert(e, app(t, b))) == w <> app(t, R.insert(e, b)) : List<&2, R.Item>}
      %Equal.sym(List<&2, R.Item>, R.insert(e, app(t, b)), app(t, R.insert(e, b)), insert_app(e, t, b, h2)) :
        {w <> _ == w <> app(t, R.insert(e, b)) : List<&2, R.Item>}
      {==}

law texts_app:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  {L.texts(app(xs, ys)) == L.texts(xs) ++ L.texts(ys) : String}

def texts_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, L.texts(app(t, ys)), L.texts(t) ++ L.texts(ys), texts_app(t, ys)) :
        {R.Item.text(x) ++ _ == (R.Item.text(x) ++ L.texts(t)) ++ L.texts(ys) : String}
      Equal.sym(String, (R.Item.text(x) ++ L.texts(t)) ++ L.texts(ys), R.Item.text(x) ++ (L.texts(t) ++ L.texts(ys)),
        Q.s_append_assoc(R.Item.text(x), L.texts(t), L.texts(ys)))

# Items below the last key
# ========================

def below_insert.go(+e: R.Item, +x: R.Item, +t: List<&2, R.Item>, +k: Nat, +c: Bool,
  h: {Nat.is_le(1n+R.Item.key(e), k) == True{} : Bool},
  ih: {any_below(R.insert(e, t), k) == True{} : Bool}) ->
  {any_below(R.insert.put(c, x, e, t, R.insert(e, t)), k) == True{} : Bool}:
  match c:
    case True{}:
      or_true_rr(Nat.is_le(1n+R.Item.key(x), k), any_below(R.insert(e, t), k), ih)
    case False{}:
      or_true_l(Nat.is_le(1n+R.Item.key(e), k), any_below(x <> t, k), h)

# An inserted item below k is below k in the buffer.
law below_insert:
  for +e: R.Item
  for +b: List<&2, R.Item>
  for +k: Nat
  for +h: {Nat.is_le(1n+R.Item.key(e), k) == True{} : Bool}
  {any_below(R.insert(e, b), k) == True{} : Bool}

def below_insert(e, b, k, h):
  match b:
    case Nil{}:
      or_true_l(Nat.is_le(1n+R.Item.key(e), k), False{}, h)
    case +x <> +t:
      below_insert.go(e, x, t, k, Nat.is_le(R.Item.key(x), R.Item.key(e)), h, below_insert(e, t, k, h))

def below_mono.go(+x: R.Item, +t: List<&2, R.Item>, +k: Nat, +k2: Nat, +c: Bool,
  ec: {Nat.is_le(1n+R.Item.key(x), k) == c : Bool},
  e: {Bool.or(c, any_below(t, k)) == True{} : Bool}, +hk: {Nat.is_le(k, k2) == True{} : Bool},
  ih: {any_below(t, k) == True{} : Bool} -> {any_below(t, k2) == True{} : Bool}) ->
  {any_below(x <> t, k2) == True{} : Bool}:
  match c:
    case True{}:
      or_true_l(Nat.is_le(1n+R.Item.key(x), k2), any_below(t, k2), Q.le_trans(1n+R.Item.key(x), k, k2, ec, hk))
    case False{}:
      or_true_rr(Nat.is_le(1n+R.Item.key(x), k2), any_below(t, k2), ih(e))

law below_mono:
  for +xs: List<&2, R.Item>
  for +k: Nat
  for +k2: Nat
  for e: {any_below(xs, k) == True{} : Bool}
  for +hk: {Nat.is_le(k, k2) == True{} : Bool}
  {any_below(xs, k2) == True{} : Bool}

def below_mono(xs, k, k2, e, hk):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, P.false_ne_true(e))
    case +x <> +t:
      below_mono.go(x, t, k, k2, Nat.is_le(1n+R.Item.key(x), k), {==}, e, hk, f => below_mono(t, k, k2, f, hk))

# Below k in xs ++ ys, with xs sorted from k' >= k: below k in ys.
law below_app_r:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +k: Nat
  for +k2: Nat
  for +hk: {Nat.is_le(k, k2) == True{} : Bool}
  for +s: {sorted_from(xs, k2) == True{} : Bool}
  for e: {any_below(app(xs, ys), k) == True{} : Bool}
  {any_below(ys, k) == True{} : Bool}

def below_app_r(xs, ys, k, k2, hk, s, e):
  match xs:
    case Nil{}:
      e
    case +x <> +t:
      +h1 = P.and_true_l(Nat.is_le(k2, R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      +h2 = P.and_true_r(Nat.is_le(k2, R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      +kx = Q.le_trans(k, k2, R.Item.key(x), hk, h1)
      below_app_r(t, ys, k, R.Item.key(x), kx, h2,
        or_cases_r(Nat.is_le(1n+R.Item.key(x), k), any_below(app(t, ys), k), e, not_s_le(R.Item.key(x), k, kx)))

# Nothing is below k in a list sorted from k' >= k.
law sorted_not_below:
  for +xs: List<&2, R.Item>
  for +k: Nat
  for +k2: Nat
  for +hk: {Nat.is_le(k, k2) == True{} : Bool}
  for +s: {sorted_from(xs, k2) == True{} : Bool}
  {any_below(xs, k) == False{} : Bool}

def sorted_not_below(xs, k, k2, hk, s):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +h1 = P.and_true_l(Nat.is_le(k2, R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      +h2 = P.and_true_r(Nat.is_le(k2, R.Item.key(x)), sorted_from(t, R.Item.key(x)), s)
      +kx = Q.le_trans(k, k2, R.Item.key(x), hk, h1)
      or_false_intro(Nat.is_le(1n+R.Item.key(x), k), any_below(t, k), not_s_le(R.Item.key(x), k, kx),
        sorted_not_below(t, k, R.Item.key(x), kx, h2))

# The spec's sort
# ===============

def ins_ins.nil(+x: R.Item, +e: R.Item, +c: Bool) ->
  {L.ins_first.put(c, x, e, Nil{}, L.ins_first(x, Nil{})) == R.insert.put(c, x, e, Nil{}, R.insert(e, Nil{})) : List<&2, R.Item>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ins_ins.ft(+x: R.Item, +y: R.Item, +e: R.Item, +t: List<&2, R.Item>, +c: Bool,
  +eA: {Nat.is_le(R.Item.key(y), R.Item.key(e)) == False{} : Bool},
  +eB: {Nat.is_le(R.Item.key(x), R.Item.key(y)) == True{} : Bool}) ->
  {L.ins_first.put(c, x, e, y <> t, L.ins_first(x, y <> t)) == R.insert.put(c, x, e, y <> t, R.insert(e, y <> t)) : List<&2, R.Item>}:
  match c:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(R.Item.key(y), R.Item.key(e)), False{}, eA) :
        {x <> e <> y <> t == x <> R.insert.put(_, y, e, t, R.insert(e, t)) : List<&2, R.Item>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(R.Item.key(x), R.Item.key(y)), True{}, eB) :
        {e <> L.ins_first.put(_, x, y, t, L.ins_first(x, t)) == e <> x <> y <> t : List<&2, R.Item>}
      {==}

def ins_ins.ff(+x: R.Item, +y: R.Item, +e: R.Item, +c: Bool,
  +eA: {Nat.is_le(R.Item.key(y), R.Item.key(e)) == False{} : Bool},
  +eB: {Nat.is_le(R.Item.key(x), R.Item.key(y)) == False{} : Bool},
  +ec: {Nat.is_le(R.Item.key(x), R.Item.key(e)) == c : Bool}) ->
  {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +a = Q.le_flip_s(R.Item.key(x), R.Item.key(y), eB)
      +b = Q.le_flip_s(R.Item.key(y), R.Item.key(e), eA)
      Empty.absurd({True{} == False{} : Bool},
        Q.le_s_not(R.Item.key(y), R.Item.key(e), Q.le_trans(1n+R.Item.key(y), R.Item.key(x), R.Item.key(e), a, ec),
          Q.le_of_s(R.Item.key(e), R.Item.key(y), b)))

def ins_ins.cons(+x: R.Item, +y: R.Item, +e: R.Item, +t: List<&2, R.Item>, +a: Bool, +b: Bool,
  +eA: {Nat.is_le(R.Item.key(y), R.Item.key(e)) == a : Bool},
  +eB: {Nat.is_le(R.Item.key(x), R.Item.key(y)) == b : Bool},
  ih: {L.ins_first(x, R.insert(e, t)) == R.insert(e, L.ins_first(x, t)) : List<&2, R.Item>}) ->
  {L.ins_first(x, R.insert.put(a, y, e, t, R.insert(e, t))) == R.insert(e, L.ins_first.put(b, x, y, t, L.ins_first(x, t))) : List<&2, R.Item>}:
  match a b:
    case True{} True{}:
      +kxe = Q.le_trans(R.Item.key(x), R.Item.key(y), R.Item.key(e), eB, eA)
      %Equal.sym(Bool, Nat.is_le(R.Item.key(x), R.Item.key(y)), True{}, eB) :
        {L.ins_first.put(_, x, y, R.insert(e, t), L.ins_first(x, R.insert(e, t))) == R.insert(e, x <> y <> t) : List<&2, R.Item>}
      %Equal.sym(Bool, Nat.is_le(R.Item.key(x), R.Item.key(e)), True{}, kxe) :
        {x <> y <> R.insert(e, t) == R.insert.put(_, x, e, y <> t, R.insert(e, y <> t)) : List<&2, R.Item>}
      %Equal.sym(Bool, Nat.is_le(R.Item.key(y), R.Item.key(e)), True{}, eA) :
        {x <> y <> R.insert(e, t) == x <> R.insert.put(_, y, e, t, R.insert(e, t)) : List<&2, R.Item>}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_le(R.Item.key(x), R.Item.key(y)), False{}, eB) :
        {L.ins_first.put(_, x, y, R.insert(e, t), L.ins_first(x, R.insert(e, t))) == R.insert(e, y <> L.ins_first(x, t)) : List<&2, R.Item>}
      %Equal.sym(Bool, Nat.is_le(R.Item.key(y), R.Item.key(e)), True{}, eA) :
        {y <> L.ins_first(x, R.insert(e, t)) == R.insert.put(_, y, e, L.ins_first(x, t), R.insert(e, L.ins_first(x, t))) : List<&2, R.Item>}
      %ih : {y <> L.ins_first(x, R.insert(e, t)) == y <> _ : List<&2, R.Item>}
      {==}
    case False{} True{}:
      ins_ins.ft(x, y, e, t, Nat.is_le(R.Item.key(x), R.Item.key(e)), eA, eB)
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_le(R.Item.key(x), R.Item.key(e)), False{},
        ins_ins.ff(x, y, e, Nat.is_le(R.Item.key(x), R.Item.key(e)), eA, eB, {==})) :
        {L.ins_first.put(_, x, e, y <> t, L.ins_first(x, y <> t)) == R.insert(e, y <> L.ins_first(x, t)) : List<&2, R.Item>}
      %Equal.sym(Bool, Nat.is_le(R.Item.key(x), R.Item.key(y)), False{}, eB) :
        {e <> L.ins_first.put(_, x, y, t, L.ins_first(x, t)) == R.insert(e, y <> L.ins_first(x, t)) : List<&2, R.Item>}
      %Equal.sym(Bool, Nat.is_le(R.Item.key(y), R.Item.key(e)), False{}, eA) :
        {e <> y <> L.ins_first(x, t) == R.insert.put(_, y, e, L.ins_first(x, t), R.insert(e, L.ins_first(x, t))) : List<&2, R.Item>}
      {==}

# The spec's insertion (before the first item no lower) and the buffer's
# (after the last item no higher) commute.
law ins_ins:
  for +x: R.Item
  for +e: R.Item
  for +ys: List<&2, R.Item>
  {L.ins_first(x, R.insert(e, ys)) == R.insert(e, L.ins_first(x, ys)) : List<&2, R.Item>}

def ins_ins(x, e, ys):
  match ys:
    case Nil{}:
      ins_ins.nil(x, e, Nat.is_le(R.Item.key(x), R.Item.key(e)))
    case +y <> +t:
      ins_ins.cons(x, y, e, t, Nat.is_le(R.Item.key(y), R.Item.key(e)), Nat.is_le(R.Item.key(x), R.Item.key(y)), {==}, {==},
        ins_ins(x, e, t))

# Sorting with one more item at the end is inserting it into the buffer.
law isort_snoc:
  for +xs: List<&2, R.Item>
  for +e: R.Item
  {L.isort(app(xs, [e])) == R.insert(e, L.isort(xs)) : List<&2, R.Item>}

def isort_snoc(xs, e):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(List<&2, R.Item>, L.isort(app(t, [e])), R.insert(e, L.isort(t)), isort_snoc(t, e)) :
        {L.ins_first(x, _) == R.insert(e, L.ins_first(x, L.isort(t))) : List<&2, R.Item>}
      ins_ins(x, e, L.isort(t))

def below_keep.go2(+x: R.Item, +t: List<&2, R.Item>, +e: R.Item, +k: Nat, +c: Bool,
  ec: {Nat.is_le(1n+R.Item.key(x), k) == c : Bool},
  d: {Bool.or(c, any_below(t, k)) == True{} : Bool},
  ih: {any_below(t, k) == True{} : Bool} -> {any_below(R.insert(e, t), k) == True{} : Bool}) ->
  {any_below(x <> R.insert(e, t), k) == True{} : Bool}:
  match c:
    case True{}:
      or_true_l(Nat.is_le(1n+R.Item.key(x), k), any_below(R.insert(e, t), k), ec)
    case False{}:
      or_true_rr(Nat.is_le(1n+R.Item.key(x), k), any_below(R.insert(e, t), k), ih(d))

def below_keep.go(+x: R.Item, +t: List<&2, R.Item>, +e: R.Item, +k: Nat, +c: Bool,
  +d: {any_below(x <> t, k) == True{} : Bool},
  ih: {any_below(t, k) == True{} : Bool} -> {any_below(R.insert(e, t), k) == True{} : Bool}) ->
  {any_below(R.insert.put(c, x, e, t, R.insert(e, t)), k) == True{} : Bool}:
  match c:
    case True{}:
      below_keep.go2(x, t, e, k, Nat.is_le(1n+R.Item.key(x), k), {==}, d, ih)
    case False{}:
      or_true_rr(Nat.is_le(1n+R.Item.key(e), k), any_below(x <> t, k), d)

# An item below k stays in the buffer after an insert.
law below_keep:
  for +e: R.Item
  for +b: List<&2, R.Item>
  for +k: Nat
  for d: {any_below(b, k) == True{} : Bool}
  {any_below(R.insert(e, b), k) == True{} : Bool}

def below_keep(e, b, k, d):
  match b:
    case Nil{}:
      Empty.absurd({any_below(R.insert(e, Nil{}), k) == True{} : Bool}, P.false_ne_true(d))
    case +x <> +t:
      below_keep.go(x, t, e, k, Nat.is_le(R.Item.key(x), R.Item.key(e)), d, f => below_keep(e, t, k, f))

def Flush.lst(f: R.Flush) -> Maybe<&2, R.Item>:
  match f:
    case R.Flushed{o, l}:
      l
    case R.Broke{o, b, p}:
      None{}

def Flush.txt(f: R.Flush) -> String:
  match f:
    case R.Flushed{o, l}:
      o
    case R.Broke{o, b, p}:
      ""

# What a flush of sorted items answers.
law flushed_last:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for -o2: String
  for -l2: Maybe<&2, R.Item>
  for +s: {sorted_from(xs, lkey(last)) == True{} : Bool}
  for e: {R.flush(xs, last) == R.Flushed{o2, l2} : R.Flush}
  {l2 == flast(xs, last) : Maybe<&2, R.Item>}

def flushed_last(xs, last, o2, l2, s, e):
  Equal.cong(R.Flush, Maybe<&2, R.Item>, f => Flush.lst(f), R.Flushed{o2, l2}, R.Flushed{L.texts(xs), flast(xs, last)},
    Equal.trans(R.Flush, R.Flushed{o2, l2}, R.flush(xs, last), R.Flushed{L.texts(xs), flast(xs, last)},
      Equal.sym(R.Flush, R.flush(xs, last), R.Flushed{o2, l2}, e), flush_sorted(xs, last, s)))

law flushed_text:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for -o2: String
  for -l2: Maybe<&2, R.Item>
  for +s: {sorted_from(xs, lkey(last)) == True{} : Bool}
  for e: {R.flush(xs, last) == R.Flushed{o2, l2} : R.Flush}
  {o2 == L.texts(xs) : String}

def flushed_text(xs, last, o2, l2, s, e):
  Equal.cong(R.Flush, String, f => Flush.txt(f), R.Flushed{o2, l2}, R.Flushed{L.texts(xs), flast(xs, last)},
    Equal.trans(R.Flush, R.Flushed{o2, l2}, R.flush(xs, last), R.Flushed{L.texts(xs), flast(xs, last)},
      Equal.sym(R.Flush, R.flush(xs, last), R.Flushed{o2, l2}, e), flush_sorted(xs, last, s)))

# Ready items and the bound on the last key
# =========================================

def all_ready(xs: List<&2, R.Item>, +w: Nat, +p: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      R.ready(w, p, x) && all_ready(t, w, p)

# The last item written (if any) was ready at input position p.
def lbound(m: Maybe<&2, R.Item>, +w: Nat, +p: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      R.ready(w, p, x)

def take_ready_ready.go(+w: Nat, +p: Nat, +x: R.Item, +t: List<&2, R.Item>, +r: Bool,
  er: {R.ready(w, p, x) == r : Bool}, ih: {all_ready(R.take_ready(w, p, t), w, p) == True{} : Bool}) ->
  {all_ready(R.take_ready.go(x <> t, r, w, p), w, p) == True{} : Bool}:
  match r:
    case True{}:
      and_intro(R.ready(w, p, x), all_ready(R.take_ready(w, p, t), w, p), er, ih)
    case False{}:
      {==}

law take_ready_ready:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  {all_ready(R.take_ready(w, p, b), w, p) == True{} : Bool}

def take_ready_ready(w, p, b):
  match b:
    case Nil{}:
      {==}
    case +x <> +t:
      take_ready_ready.go(w, p, x, t, R.ready(w, p, x), {==}, take_ready_ready(w, p, t))

law flast_bound:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for +w: Nat
  for +p: Nat
  for +hl: {lbound(last, w, p) == True{} : Bool}
  for +hx: {all_ready(xs, w, p) == True{} : Bool}
  {lbound(flast(xs, last), w, p) == True{} : Bool}

def flast_bound(xs, last, w, p, hl, hx):
  match xs:
    case Nil{}:
      hl
    case +x <> +t:
      flast_bound(t, Some{x}, w, p, P.and_true_l(R.ready(w, p, x), all_ready(t, w, p), hx), P.and_true_r(R.ready(w, p, x), all_ready(t, w, p), hx))

law lbound_mono:
  for +last: Maybe<&2, R.Item>
  for +w: Nat
  for +p: Nat
  for +q: Nat
  for +hl: {lbound(last, w, p) == True{} : Bool}
  for +hpq: {Nat.is_le(p, q) == True{} : Bool}
  {lbound(last, w, q) == True{} : Bool}

def lbound_mono(last, w, p, q, hl, hpq):
  match last:
    case None{}:
      {==}
    case Some{+x}:
      Q.le_trans(Nat.add(R.Item.key(x), w), p, q, hl, hpq)

# The last key written is at most the key of a later line that moved left by
# less than w.
law key_ok:
  for +last: Maybe<&2, R.Item>
  for +w: Nat
  for +pa: Nat
  for +pz: Nat
  for +kz: Nat
  for +hl: {lbound(last, w, pa) == True{} : Bool}
  for +hp: {Nat.is_le(pa, pz) == True{} : Bool}
  for +hm: {Nat.is_lt(pz, Nat.add(kz, w)) == True{} : Bool}
  {Nat.is_le(lkey(last), kz) == True{} : Bool}

def key_ok(last, w, pa, pz, kz, hl, hp, hm):
  match last:
    case None{}:
      P.le_zero_l(kz)
    case Some{+x}:
      +kx = R.Item.key(x)
      +a = Q.le_trans(Nat.add(kx, w), pa, pz, hl, hp)
      +b = Q.le_trans(1n+Nat.add(kx, w), 1n+pz, Nat.add(kz, w), a, Q.lt_le_s(pz, Nat.add(kz, w), hm))
      Q.le_of_s(kx, kz, Q.le_add_cancel(1n+kx, kz, w, b))
