import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm_seq.bend as Norm
import ./bytes_enc.bend as E
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_u32.bend as U

# Lemmas for proof_b_cache.bend that hold no buffer: Nat facts, the reads
# Norm.parts asks (for an abstract bound k), and taking and dropping letters.

# ---------------------------------------------------------------------------
# Nat
# ---------------------------------------------------------------------------

def le_zero_eq(+x: Nat, h: {Nat.is_le(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, N.false_ne_true(h))

def sub_le(+x: Nat, +k: Nat) -> {Nat.is_le(Nat.sub(x, k), x) == True{} : Bool}:
  match x k:
    case 0n _:
      {==}
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), N.lt_to_le(p, 1n+p, Equal.trans(Bool, Nat.is_lt(p, 1n+p), Nat.is_le(p, p), True{}, N.lt_succ_iff(p, p), N.le_refl(p))))

def sub_sub(+m: Nat, +a: Nat, +k: Nat) -> {Nat.sub(Nat.sub(m, a), k) == Nat.sub(m, Nat.add(a, k)) : Nat}:
  match m a:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, k)

# x <= 1 + f and k >= 1: x - k <= f.
def sub_step(+x: Nat, +k: Nat, +f: Nat, hx: {Nat.is_le(x, 1n+f) == True{} : Bool}, hk: {Nat.is_le(1n, k) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(x, k), f) == True{} : Bool}:
  match x k:
    case 0n _:
      N.le_zero_l(f)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, 0n), f) == True{} : Bool}, N.false_ne_true(hk))
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, f, sub_le(p, q), hx)


# 1 + p < (1 + p) + (1 + p).
def PL_twice(+p: Nat) -> {Nat.is_lt(1n+p, Nat.add(1n+p, 1n+p)) == True{} : Bool}:
  %N.add_zero(1n+p) : {Nat.is_lt(_, Nat.add(1n+p, 1n+p)) == True{} : Bool}
  N.lt_add_l(1n+p, 0n, 1n+p, {==})

# h < h + y: y > 0.
def lt_sub0(+h: Nat, +y: Nat, +e: {Nat.is_lt(h, Nat.add(h, y)) == True{} : Bool}) -> {Nat.is_lt(0n, y) == True{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(h, Nat.add(h, 0n)), True{}, Equal.sym(Bool, Nat.is_lt(h, Nat.add(h, 0n)), False{}, AB.subst(Nat, z => {Nat.is_lt(h, z) == False{} : Bool}, h, Nat.add(h, 0n), Equal.sym(Nat, Nat.add(h, 0n), h, N.add_zero(h)), N.lt_irrefl(h))), e)))
    case 1n+q:
      {==}

def add_le2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(c, d) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  N.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), N.le_add_mono_r(c, a, b, h1), N.le_add_mono_l(b, c, d, h2))

# ---------------------------------------------------------------------------
# le31 (n is at most 2^31, in word form)
# ---------------------------------------------------------------------------

def le31_fit(+n: Nat, +h: {Norm.le31(n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(n)) == n : Nat}:
  N.eq_sound(U32.to_nat(U32.from_nat(n)), n, N.and_true_l(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), U32.is_le(U32.from_nat(n), 2147483648), h))

# n <= m and from_nat(m) <= w (as words), both fitting: from_nat(n) <= w.
def mono_w(+n: Nat, +m: Nat, +w: U32,
  +h: {Nat.is_le(n, m) == True{} : Bool},
  +en: {U32.to_nat(U32.from_nat(n)) == n : Nat},
  +em: {U32.to_nat(U32.from_nat(m)) == m : Nat},
  +hm: {U32.is_le(U32.from_nat(m), w) == True{} : Bool}) ->
  {U32.is_le(U32.from_nat(n), w) == True{} : Bool}:
  +hm2 = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat(w)) == True{} : Bool}, U32.to_nat(U32.from_nat(m)), m, em,
    Equal.trans(Bool, Nat.is_le(U32.to_nat(U32.from_nat(m)), U32.to_nat(w)), U32.is_le(U32.from_nat(m), w), True{}, Equal.sym(Bool, U32.is_le(U32.from_nat(m), w), Nat.is_le(U32.to_nat(U32.from_nat(m)), U32.to_nat(w)), U.is_le_to_nat(U32.from_nat(m), w)), hm))
  %Equal.sym(Bool, U32.is_le(U32.from_nat(n), w), Nat.is_le(U32.to_nat(U32.from_nat(n)), U32.to_nat(w)), U.is_le_to_nat(U32.from_nat(n), w)) : {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, en) : {Nat.is_le(_, U32.to_nat(w)) == True{} : Bool}
  N.le_trans(n, m, U32.to_nat(w), h, hm2)

# le31 is closed downwards.
def le31_mono(+n: Nat, +m: Nat, +h: {Nat.is_le(n, m) == True{} : Bool}, +hm: {Norm.le31(m) == True{} : Bool}) ->
  {Norm.le31(n) == True{} : Bool}:
  +em = le31_fit(m, hm)
  +hw = N.and_true_r(Nat.is_eq(U32.to_nat(U32.from_nat(m)), m), U32.is_le(U32.from_nat(m), 2147483648), hm)
  +hlt = N.le_lt_trans(n, m, Nat.pow(2n, 32n), h, AB.subst(Nat, z => {Nat.is_lt(z, Nat.pow(2n, 32n)) == True{} : Bool}, U32.to_nat(U32.from_nat(m)), m, em, U.to_nat_lt_p(U32.from_nat(m))))
  +en = Equal.trans(Nat, U32.to_nat(U32.from_nat(n)), Nat.mod(n, Nat.pow(2n, 32n)), n, U.to_nat_from_nat_p(n), U.wrap_small_p(n, hlt))
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, en) : {Bool.and(Nat.is_eq(_, n), U32.is_le(U32.from_nat(n), 2147483648)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(n, n), True{}, N.eq_refl(n)) : {Bool.and(_, U32.is_le(U32.from_nat(n), 2147483648)) == True{} : Bool}
  mono_w(n, m, 2147483648, h, en, em, hw)

def gt31.k(+x: Nat, +k: Nat, +q: Bool,
  +hq: {Nat.is_le(x, k) == q : Bool},
  +hk31: {Norm.le31(k) == True{} : Bool},
  +hx: {Norm.le31(x) == False{} : Bool}) ->
  {Nat.is_lt(k, x) == True{} : Bool}:
  match q:
    case True{}:
      Empty.absurd({Nat.is_lt(k, x) == True{} : Bool}, N.true_ne_false(Equal.trans(Bool, True{}, Norm.le31(x), False{}, Equal.sym(Bool, Norm.le31(x), True{}, le31_mono(x, k, hq, hk31)), hx)))
    case False{}:
      N.not_le_lt(x, k, hq)

# A read that does not fit le31 is longer than k (le31(k)).
def gt31(+x: Nat, +k: Nat, +hk31: {Norm.le31(k) == True{} : Bool}, +hx: {Norm.le31(x) == False{} : Bool}) ->
  {Nat.is_lt(k, x) == True{} : Bool}:
  gt31.k(x, k, Nat.is_le(x, k), {==}, hk31, hx)

# ---------------------------------------------------------------------------
# Letters (copied from proof_machine_ask.bend, same author)
# ---------------------------------------------------------------------------

def word_cmp_refl(+n: Nat, +w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, word_cmp_refl(p, at)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}
        case WCon{False{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, word_cmp_refl(p, at)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}

def order_refl(+s: String) -> {String.order.go(s, s, EQ{}) == EQ{} : Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{U32{w}}, t}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_refl(32n, w)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      order_refl(t)

def str_eq_refl(+s: String) -> {String.eq(s, s) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(s, s, EQ{}), EQ{}, order_refl(s)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def drop_min(+r: String, +f: Nat) -> {String.drop(r, Nat.min(f, String.length(r))) == String.drop(r, f) : String}:
  match r f:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      drop_min(t, p)

def take_len_take(+x: String, +k: Nat) -> {String.take(x, String.length(String.take(x, k))) == String.take(x, k) : String}:
  match x k:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %take_len_take(t, p) : {SCon{h, String.take(t, String.length(String.take(t, p)))} == SCon{h, _} : String}
      {==}

def min_mono(+e: Nat, +y: Nat, +l: Nat, h: {Nat.is_le(e, y) == True{} : Bool}) ->
  {Nat.is_le(Nat.min(e, l), Nat.min(y, l)) == True{} : Bool}:
  match e y l:
    case 0n _ _:
      N.le_zero_l(Nat.min(y, l))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(Nat.min(1n+p, l), Nat.min(0n, l)) == True{} : Bool}, N.false_ne_true(h))
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+m:
      min_mono(p, q, m, h)

def le_max_l(+e: Nat, +z: Nat) -> {Nat.is_le(e, Nat.max(e, z)) == True{} : Bool}:
  match e z:
    case 0n _:
      N.le_zero_l(z)
    case 1n+p 0n:
      N.le_refl(p)
    case 1n+p 1n+q:
      le_max_l(p, q)

# ---------------------------------------------------------------------------
# Lists of bytes
# ---------------------------------------------------------------------------

def drop0(+xs: List<&2, U32>) -> {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def take_all(+xs: List<&2, U32>) -> {List.take(&2, U32, xs, List.length(&2, U32, xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %take_all(t) : {Con{h, List.take(&2, U32, t, List.length(&2, U32, t))} == Con{h, _} : List<&2, U32>}
      {==}

# ---------------------------------------------------------------------------
# Taking, dropping and joining letters
# ---------------------------------------------------------------------------

def take_len(+x: String, +k: Nat) -> {String.length(String.take(x, k)) == Nat.min(k, String.length(x)) : Nat}:
  match x k:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %take_len(t, p) : {1n+String.length(String.take(t, p)) == 1n+_ : Nat}
      {==}

def min_le_l(+k: Nat, +l: Nat) -> {Nat.is_le(Nat.min(k, l), k) == True{} : Bool}:
  match k l:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_l(p, q)

def take_len_le(+x: String, +k: Nat) -> {Nat.is_le(String.length(String.take(x, k)), k) == True{} : Bool}:
  %Equal.sym(Nat, String.length(String.take(x, k)), Nat.min(k, String.length(x)), take_len(x, k)) : {Nat.is_le(_, k) == True{} : Bool}
  min_le_l(k, String.length(x))

def bytes_take(+s: String, +n: Nat, +h: {E.is_bytes(s) == True{} : Bool}) -> {E.is_bytes(String.take(s, n)) == True{} : Bool}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{c, t} 0n:
      {==}
    case SCon{c, t} 1n+p:
      +hc = N.and_true_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), h)
      +ht = N.and_true_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), h)
      %Equal.sym(Bool, U32.is_lt(Char.to_u32(c), 256), True{}, hc) : {Bool.and(_, E.is_bytes(String.take(t, p))) == True{} : Bool}
      bytes_take(t, p, ht)

def bytes_drop(+s: String, +n: Nat, +h: {E.is_bytes(s) == True{} : Bool}) -> {E.is_bytes(String.drop(s, n)) == True{} : Bool}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{c, t} 0n:
      h
    case SCon{c, t} 1n+p:
      bytes_drop(t, p, N.and_true_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), h))

def drop_drop_s(+r: String, +a: Nat, +i: Nat) -> {String.drop(String.drop(r, a), i) == String.drop(r, Nat.add(a, i)) : String}:
  match r a:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      drop_drop_s(t, p, i)

def take_app_s(+s: String, +i: Nat, +j: Nat) ->
  {String.append(String.take(s, i), String.take(String.drop(s, i), j)) == String.take(s, Nat.add(i, j)) : String}:
  match s i:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %take_app_s(t, p, j) : {SCon{h, String.append(String.take(t, p), String.take(String.drop(t, p), j))} == SCon{h, _} : String}
      {==}

def str_nil(+a: String) -> {String.append(a, "") == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %str_nil(t) : {SCon{h, String.append(t, "")} == SCon{h, _} : String}
      {==}

def sub_add_sub(+a: Nat, +m: Nat, +b: Nat,
  +ham: {Nat.is_le(a, m) == True{} : Bool},
  +hmb: {Nat.is_le(m, b) == True{} : Bool}) ->
  {Nat.add(Nat.sub(m, a), Nat.sub(b, m)) == Nat.sub(b, a) : Nat}:
  match a m b:
    case 0n _ _:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, N.sub_zero(m)) : {Nat.add(_, Nat.sub(b, m)) == Nat.sub(b, 0n) : Nat}
      %Equal.sym(Nat, Nat.sub(b, 0n), b, N.sub_zero(b)) : {Nat.add(m, Nat.sub(b, m)) == _ : Nat}
      N.le_sub_add(m, b, hmb)
    case 1n+p 0n _:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+p), Nat.sub(b, 0n)) == Nat.sub(b, 1n+p) : Nat}, N.false_ne_true(ham))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.add(Nat.sub(1n+q, 1n+p), Nat.sub(0n, 1n+q)) == Nat.sub(0n, 1n+p) : Nat}, N.false_ne_true(hmb))
    case 1n+p 1n+q 1n+s:
      sub_add_sub(p, q, s, ham, hmb)

# k < b - a: a + k <= b.
def le_add_of_sub(+a: Nat, +k: Nat, +b: Nat, +h: {Nat.is_lt(k, Nat.sub(b, a)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, k), b) == True{} : Bool}:
  match a b:
    case 0n _:
      N.lt_to_le(k, b, AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, Nat.sub(b, 0n), b, N.sub_zero(b), h))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+p, k), 0n) == True{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, N.lt_zero(k)), h)))
    case 1n+p 1n+q:
      le_add_of_sub(p, k, q, h)

def take0_s(+x: String) -> {String.take(x, 0n) == "" : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def drop0_s(+x: String) -> {String.drop(x, 0n) == x : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# Taking the first min(q, len t) of the first q0 letters, when that is
# within q0: the first q letters.
def tt(+t: String, +q0: Nat, +q: Nat,
  +h: {Nat.is_le(Nat.min(q, String.length(t)), Nat.min(q0, String.length(t))) == True{} : Bool}) ->
  {String.take(String.take(t, q0), Nat.min(q, String.length(t))) == String.take(t, q) : String}:
  match t q0 q:
    case SNil{} _ _:
      {==}
    case SCon{x, u} _ 0n:
      take0_s(String.take(SCon{x, u}, q0))
    case SCon{x, u} 0n 1n+p:
      Empty.absurd({String.take(String.take(SCon{x, u}, 0n), Nat.min(1n+p, String.length(SCon{x, u}))) == String.take(SCon{x, u}, 1n+p) : String}, N.false_ne_true(h))
    case SCon{x, u} 1n+p0 1n+p:
      %tt(u, p0, p, h) : {SCon{x, String.take(String.take(u, p0), Nat.min(p, String.length(u)))} == SCon{x, _} : String}
      {==}

def len0(+s: String, +h: {String.length(s) == 0n : Nat}) -> {s == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, t}:
      Empty.absurd({SCon{x, t} == "" : String}, N.succ_ne_zero(String.length(t), h))

def codes_take(+s: String, +n: Nat) -> {E.codes(String.take(s, n)) == List.take(&2, U32, E.codes(s), n) : List<&2, U32>}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{x, t} 0n:
      {==}
    case SCon{x, t} 1n+p:
      %codes_take(t, p) : {Con{Char.to_u32(x), E.codes(String.take(t, p))} == Con{Char.to_u32(x), _} : List<&2, U32>}
      {==}

def codes_drop(+s: String, +n: Nat) -> {E.codes(String.drop(s, n)) == List.drop(&2, U32, E.codes(s), n) : List<&2, U32>}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{x, t} 0n:
      {==}
    case SCon{x, t} 1n+p:
      codes_drop(t, p)

def sub_mono(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, c), Nat.sub(b, c)) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      N.le_zero_l(Nat.sub(b, c))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, c), Nat.sub(0n, c)) == True{} : Bool}, N.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h
    case 1n+p 1n+q 1n+r:
      sub_mono(p, q, r, h)

# x - y = 1 + k: y <= x.
def sub_pos(+x: Nat, +y: Nat, +k: Nat, +h: {Nat.sub(x, y) == 1n+k : Nat}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n _:
      Empty.absurd({Nat.is_le(y, 0n) == True{} : Bool}, N.zero_ne_succ(k, h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_pos(p, q, k, h)

# m <= x + y and x <= m: m - x <= y... (the parts of a sum are within it).
def le_add_l2(+x: Nat, +y: Nat, +z: Nat, +h: {Nat.is_le(Nat.add(x, y), z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  N.le_trans(x, Nat.add(x, y), z, N.le_add_r(x, y), h)

def le_add_r2(+x: Nat, +y: Nat, +z: Nat, +h: {Nat.is_le(Nat.add(x, y), z) == True{} : Bool}) -> {Nat.is_le(y, z) == True{} : Bool}:
  N.le_trans(y, Nat.add(x, y), z, N.le_add_l(y, x), h)

# ---------------------------------------------------------------------------
# Halves (Nat.div by 2)
# ---------------------------------------------------------------------------

def HV(+x: Nat) -> Nat:
  Nat.div(x, 2n)

# h + h + x % 2 = x, with h = x / 2.
def half_eq(+x: Nat) -> {Nat.add(Nat.add(HV(x), HV(x)), Nat.mod(x, 2n)) == x : Nat}:
  %Equal.trans(Nat, Nat.mul(HV(x), 2n), Nat.double(HV(x)), Nat.add(HV(x), HV(x)), N.mul2_r(HV(x)), N.dbl_add(HV(x))) :
    {Nat.add(_, Nat.mod(x, 2n)) == x : Nat}
  N.div_mod(x, 2n)

def half_le2.k(+x: Nat, +h: Nat, +q: Nat, +e: {Nat.add(Nat.add(h, h), q) == x : Nat}, +hq: {Nat.is_lt(q, 2n) == True{} : Bool},
  +hx: {Nat.is_le(2n, x) == True{} : Bool}) -> {Nat.is_le(1n, h) == True{} : Bool}:
  match h:
    case 0n:
      +hx2 = AB.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, x, q, Equal.sym(Nat, q, x, e), hx)
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, N.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(2n, q), False{}, Equal.sym(Bool, Nat.is_le(2n, q), True{}, hx2), Equal.trans(Bool, Nat.is_le(2n, q), Nat.is_lt(1n, q), False{}, N.le_succ_lt(1n, q), N.le_not_lt(q, 1n, Equal.trans(Bool, Nat.is_le(q, 1n), Nat.is_lt(q, 2n), True{}, Equal.sym(Bool, Nat.is_lt(q, 2n), Nat.is_le(q, 1n), N.lt_succ_iff(q, 1n)), hq))))))
    case 1n+p:
      N.le_zero_l(p)

# x >= 2: x / 2 >= 1.
def half_pos(+x: Nat, +hx: {Nat.is_le(2n, x) == True{} : Bool}) -> {Nat.is_le(1n, HV(x)) == True{} : Bool}:
  half_le2.k(x, HV(x), Nat.mod(x, 2n), half_eq(x), N.mod_lt(x, 2n, {==}), hx)

def half_lt.k(+x: Nat, +h: Nat, +q: Nat, +e: {Nat.add(Nat.add(h, h), q) == x : Nat},
  +hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_lt(h, x) == True{} : Bool}:
  match h:
    case 0n:
      Equal.trans(Bool, Nat.is_lt(0n, x), Nat.is_le(1n, x), True{}, Equal.sym(Bool, Nat.is_le(1n, x), Nat.is_lt(0n, x), N.le_succ_lt(0n, x)), hx)
    case 1n+p:
      AB.subst(Nat, z => {Nat.is_lt(1n+p, z) == True{} : Bool}, Nat.add(Nat.add(1n+p, 1n+p), q), x, e,
        N.lt_le_trans(1n+p, Nat.add(1n+p, 1n+p), Nat.add(Nat.add(1n+p, 1n+p), q), PL_twice(p), N.le_add_r(Nat.add(1n+p, 1n+p), q)))

# x >= 1: x / 2 < x.
def half_lt(+x: Nat, +hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_lt(HV(x), x) == True{} : Bool}:
  half_lt.k(x, HV(x), Nat.mod(x, 2n), half_eq(x), hx)

# x - x/2 >= 1 when x >= 1, and x/2 + (x - x/2) = x.
def half_rest(+x: Nat, +hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.add(HV(x), Nat.sub(x, HV(x))) == x : Nat}:
  N.le_sub_add(HV(x), x, N.lt_to_le(HV(x), x, half_lt(x, hx)))

# ---------------------------------------------------------------------------
# The reads of a window (parts.go: one read, or the two halves)
# ---------------------------------------------------------------------------

# Every read passes le31 (E.reqs_ok, once the contract tests le31).
def rok31(rs: List<&2, Pr.Req>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Pr.Req{c, a, b}, t}:
      Norm.le31(Nat.sub(b, a)) && rok31(t)

# The first read is from a, on contig c.
def hd1(rs: List<&2, Pr.Req>, +c: String, +a: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{Pr.Req{c1, a1, e1}, t}:
      String.eq(c1, c) && Nat.is_eq(a1, a)

# Every read is on contig c.
def allc(rs: List<&2, Pr.Req>, +c: String) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Pr.Req{c1, a1, e1}, t}:
      String.eq(c1, c) && allc(t, c)

def PGL(+fuel: Nat, +one: Bool, +c: String, +a: Nat, +b: Nat) -> Nat:
  List.length(&2, Pr.Req, Norm.parts.go(fuel, one, c, a, b))

def len_app(+xs: List<&2, Pr.Req>, +ys: List<&2, Pr.Req>) ->
  {List.length(&2, Pr.Req, List.append(&2, Pr.Req, xs, ys)) == Nat.add(List.length(&2, Pr.Req, xs), List.length(&2, Pr.Req, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %len_app(t, ys) : {1n+List.length(&2, Pr.Req, List.append(&2, Pr.Req, t, ys)) == 1n+_ : Nat}
      {==}

def rok31_app(+xs: List<&2, Pr.Req>, +ys: List<&2, Pr.Req>, +hx: {rok31(xs) == True{} : Bool}, +hy: {rok31(ys) == True{} : Bool}) ->
  {rok31(List.append(&2, Pr.Req, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{Pr.Req{c, a, b}, t}:
      +h1 = N.and_true_l(Norm.le31(Nat.sub(b, a)), rok31(t), hx)
      %Equal.sym(Bool, Norm.le31(Nat.sub(b, a)), True{}, h1) : {Bool.and(_, rok31(List.append(&2, Pr.Req, t, ys))) == True{} : Bool}
      rok31_app(t, ys, N.and_true_r(Norm.le31(Nat.sub(b, a)), rok31(t), hx), hy)

def allc_app(+xs: List<&2, Pr.Req>, +ys: List<&2, Pr.Req>, +c: String, +hx: {allc(xs, c) == True{} : Bool}, +hy: {allc(ys, c) == True{} : Bool}) ->
  {allc(List.append(&2, Pr.Req, xs, ys), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{Pr.Req{c1, a1, e1}, t}:
      +h1 = N.and_true_l(String.eq(c1, c), allc(t, c), hx)
      %Equal.sym(Bool, String.eq(c1, c), True{}, h1) : {Bool.and(_, allc(List.append(&2, Pr.Req, t, ys), c)) == True{} : Bool}
      allc_app(t, ys, c, N.and_true_r(String.eq(c1, c), allc(t, c), hx), hy)

def hd1_app(+xs: List<&2, Pr.Req>, +ys: List<&2, Pr.Req>, +c: String, +a: Nat, +hx: {hd1(xs, c, a) == True{} : Bool}) ->
  {hd1(List.append(&2, Pr.Req, xs, ys), c, a) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({hd1(ys, c, a) == True{} : Bool}, N.false_ne_true(hx))
    case Con{Pr.Req{c1, a1, e1}, t}:
      hx

def last_app(+xs: List<&2, Pr.Req>, +ys: List<&2, Pr.Req>, +z: Nat) ->
  {Norm.last_b(List.append(&2, Pr.Req, xs, ys), z) == Norm.last_b(ys, Norm.last_b(xs, z)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{Pr.Req{c, a, b}, t}:
      last_app(t, ys, b)

# A read that fits is one read (parts.go matches its fuel first).
def pp_true(+fuel: Nat, +c: String, +a: Nat, +b: Nat) ->
  {Norm.parts.go(fuel, True{}, c, a, b) == [Pr.Req{c, a, b}] : List<&2, Pr.Req>}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      {==}

def PM(+a: Nat, +b: Nat) -> Nat:
  Nat.add(a, HV(Nat.sub(b, a)))

def pl1(+fuel: Nat, +one: Bool, +c: String, +a: Nat, +b: Nat) -> {Nat.is_le(1n, PGL(fuel, one, c, a, b)) == True{} : Bool}:
  match fuel one:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+f False{}:
      +m = PM(a, b)
      +l1 = PGL(f, Norm.le31(Nat.sub(m, a)), c, a, m)
      +l2 = PGL(f, Norm.le31(Nat.sub(b, m)), c, m, b)
      %Equal.sym(Nat, List.length(&2, Pr.Req, List.append(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))), Nat.add(List.length(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m)), List.length(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))), len_app(Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))) : {Nat.is_le(1n, _) == True{} : Bool}
      N.le_trans(1n, l1, Nat.add(l1, l2), pl1(f, Norm.le31(Nat.sub(m, a)), c, a, m), N.le_add_r(l1, l2))

def ph(+fuel: Nat, +one: Bool, +c: String, +a: Nat, +b: Nat) -> {hd1(Norm.parts.go(fuel, one, c, a, b), c, a) == True{} : Bool}:
  match fuel one:
    case _ True{}:
      %Equal.sym(Bool, String.eq(c, c), True{}, str_eq_refl(c)) : {Bool.and(_, Nat.is_eq(a, a)) == True{} : Bool}
      N.eq_refl(a)
    case 0n False{}:
      %Equal.sym(Bool, String.eq(c, c), True{}, str_eq_refl(c)) : {Bool.and(_, Nat.is_eq(a, a)) == True{} : Bool}
      N.eq_refl(a)
    case 1n+f False{}:
      +m = PM(a, b)
      hd1_app(Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b), c, a, ph(f, Norm.le31(Nat.sub(m, a)), c, a, m))

def pallc(+fuel: Nat, +one: Bool, +c: String, +a: Nat, +b: Nat) -> {allc(Norm.parts.go(fuel, one, c, a, b), c) == True{} : Bool}:
  match fuel one:
    case _ True{}:
      %Equal.sym(Bool, String.eq(c, c), True{}, str_eq_refl(c)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case 0n False{}:
      %Equal.sym(Bool, String.eq(c, c), True{}, str_eq_refl(c)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case 1n+f False{}:
      +m = PM(a, b)
      allc_app(Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b), c, pallc(f, Norm.le31(Nat.sub(m, a)), c, a, m), pallc(f, Norm.le31(Nat.sub(b, m)), c, m, b))

def plast(+fuel: Nat, +one: Bool, +c: String, +a: Nat, +b: Nat, +z: Nat) -> {Norm.last_b(Norm.parts.go(fuel, one, c, a, b), z) == b : Nat}:
  match fuel one:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+f False{}:
      +m = PM(a, b)
      +xs = Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m)
      +ys = Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b)
      %Equal.sym(Nat, Norm.last_b(List.append(&2, Pr.Req, xs, ys), z), Norm.last_b(ys, Norm.last_b(xs, z)), last_app(xs, ys, z)) : {_ == b : Nat}
      plast(f, Norm.le31(Nat.sub(b, m)), c, m, b, Norm.last_b(xs, z))

# fuel 0 with a read that does not fit: impossible (le31(0) holds).
def pg_none(+a: Nat, +b: Nat, -T: Type,
  +ho: {Norm.le31(Nat.sub(b, a)) == False{} : Bool},
  +hf: {Nat.is_le(Nat.sub(b, a), 0n) == True{} : Bool}) -> T:
  +h0 = le_zero_eq(Nat.sub(b, a), hf)
  +e = AB.subst(Nat, z => {Norm.le31(z) == False{} : Bool}, Nat.sub(b, a), 0n, h0, ho)
  Empty.absurd(T, N.true_ne_false(e))

# A read that does not fit has at least 2 letters.
def two_of(+x: Nat, +ho: {Norm.le31(x) == False{} : Bool}) -> {Nat.is_le(2n, x) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(2n, x), Nat.is_lt(1n, x), True{}, N.le_succ_lt(1n, x), gt31(x, 1n, {==}, ho))

# The halves of a read that does not fit, with fuel 1 + f >= b - a: each
# half within f, and their sizes.
def hm_a(+a: Nat, +b: Nat) -> {Nat.sub(PM(a, b), a) == HV(Nat.sub(b, a)) : Nat}:
  N.sub_add_l(a, HV(Nat.sub(b, a)))

def hm_b(+a: Nat, +b: Nat) -> {Nat.sub(b, PM(a, b)) == Nat.sub(Nat.sub(b, a), HV(Nat.sub(b, a))) : Nat}:
  Equal.sym(Nat, Nat.sub(Nat.sub(b, a), HV(Nat.sub(b, a))), Nat.sub(b, PM(a, b)), sub_sub(b, a, HV(Nat.sub(b, a))))

def hf_a(+f: Nat, +a: Nat, +b: Nat, +ho: {Norm.le31(Nat.sub(b, a)) == False{} : Bool}, +hf: {Nat.is_le(Nat.sub(b, a), 1n+f) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(PM(a, b), a), f) == True{} : Bool}:
  +x = Nat.sub(b, a)
  +h1 = N.le_trans(1n, 2n, x, {==}, two_of(x, ho))
  %Equal.sym(Nat, Nat.sub(PM(a, b), a), HV(x), hm_a(a, b)) : {Nat.is_le(_, f) == True{} : Bool}
  Equal.trans(Bool, Nat.is_le(HV(x), f), Nat.is_lt(HV(x), 1n+f), True{}, Equal.sym(Bool, Nat.is_lt(HV(x), 1n+f), Nat.is_le(HV(x), f), N.lt_succ_iff(HV(x), f)), N.lt_le_trans(HV(x), x, 1n+f, half_lt(x, h1), hf))

def hf_b(+f: Nat, +a: Nat, +b: Nat, +ho: {Norm.le31(Nat.sub(b, a)) == False{} : Bool}, +hf: {Nat.is_le(Nat.sub(b, a), 1n+f) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(b, PM(a, b)), f) == True{} : Bool}:
  +x = Nat.sub(b, a)
  %Equal.sym(Nat, Nat.sub(b, PM(a, b)), Nat.sub(x, HV(x)), hm_b(a, b)) : {Nat.is_le(_, f) == True{} : Bool}
  sub_step(x, HV(x), f, hf, half_pos(x, two_of(x, ho)))

def p31(+fuel: Nat, +one: Bool, +c: String, +a: Nat, +b: Nat,
  +ho: {Norm.le31(Nat.sub(b, a)) == one : Bool},
  +hf: {Nat.is_le(Nat.sub(b, a), fuel) == True{} : Bool}) ->
  {rok31(Norm.parts.go(fuel, one, c, a, b)) == True{} : Bool}:
  match fuel one:
    case _ True{}:
      %Equal.sym(Bool, Norm.le31(Nat.sub(b, a)), True{}, ho) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case 0n False{}:
      pg_none(a, b, {rok31(Norm.parts.go(0n, False{}, c, a, b)) == True{} : Bool}, ho, hf)
    case 1n+f False{}:
      +m = PM(a, b)
      rok31_app(Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b),
        p31(f, Norm.le31(Nat.sub(m, a)), c, a, m, {==}, hf_a(f, a, b, ho, hf)),
        p31(f, Norm.le31(Nat.sub(b, m)), c, m, b, {==}, hf_b(f, a, b, ho, hf)))

def max1(+y: Nat, +h: {Nat.is_le(1n, y) == True{} : Bool}) -> {Nat.max(1n, y) == y : Nat}:
  match y:
    case 0n:
      Empty.absurd({Nat.max(1n, 0n) == 0n : Nat}, N.false_ne_true(h))
    case 1n+p:
      {==}

def le_max_r1(+y: Nat) -> {Nat.is_le(y, Nat.max(1n, y)) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+p:
      N.le_refl(1n+p)

def pmax(+fuel: Nat, +one: Bool, +c: String, +a: Nat, +b: Nat,
  +ho: {Norm.le31(Nat.sub(b, a)) == one : Bool},
  +hf: {Nat.is_le(Nat.sub(b, a), fuel) == True{} : Bool}) ->
  {Nat.is_le(PGL(fuel, one, c, a, b), Nat.max(1n, Nat.sub(b, a))) == True{} : Bool}:
  match fuel one:
    case _ True{}:
      le_max_l(1n, Nat.sub(b, a))
    case 0n False{}:
      le_max_l(1n, Nat.sub(b, a))
    case 1n+f False{}:
      +x = Nat.sub(b, a)
      +m = PM(a, b)
      +h = HV(x)
      +l1 = PGL(f, Norm.le31(Nat.sub(m, a)), c, a, m)
      +l2 = PGL(f, Norm.le31(Nat.sub(b, m)), c, m, b)
      +hx1 = N.le_trans(1n, 2n, x, {==}, two_of(x, ho))
      +i1 = AB.subst(Nat, z => {Nat.is_le(l1, z) == True{} : Bool}, Nat.max(1n, Nat.sub(m, a)), h,
        Equal.trans(Nat, Nat.max(1n, Nat.sub(m, a)), Nat.max(1n, h), h, Equal.cong(Nat, Nat, z => Nat.max(1n, z), Nat.sub(m, a), h, hm_a(a, b)), max1(h, half_pos(x, two_of(x, ho)))),
        pmax(f, Norm.le31(Nat.sub(m, a)), c, a, m, {==}, hf_a(f, a, b, ho, hf)))
      +hr1 = AB.subst(Nat, z => {Nat.is_lt(h, z) == True{} : Bool}, x, Nat.add(h, Nat.sub(x, h)), Equal.sym(Nat, Nat.add(h, Nat.sub(x, h)), x, half_rest(x, hx1)), half_lt(x, hx1))
      +hpos2 = Equal.trans(Bool, Nat.is_le(1n, Nat.sub(x, h)), Nat.is_lt(0n, Nat.sub(x, h)), True{}, N.le_succ_lt(0n, Nat.sub(x, h)), lt_sub0(h, Nat.sub(x, h), hr1))
      +i2 = AB.subst(Nat, z => {Nat.is_le(l2, z) == True{} : Bool}, Nat.max(1n, Nat.sub(b, m)), Nat.sub(x, h),
        Equal.trans(Nat, Nat.max(1n, Nat.sub(b, m)), Nat.max(1n, Nat.sub(x, h)), Nat.sub(x, h), Equal.cong(Nat, Nat, z => Nat.max(1n, z), Nat.sub(b, m), Nat.sub(x, h), hm_b(a, b)), max1(Nat.sub(x, h), hpos2)),
        pmax(f, Norm.le31(Nat.sub(b, m)), c, m, b, {==}, hf_b(f, a, b, ho, hf)))
      %Equal.sym(Nat, List.length(&2, Pr.Req, List.append(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))), Nat.add(List.length(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m)), List.length(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))), len_app(Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))) : {Nat.is_le(_, Nat.max(1n, x)) == True{} : Bool}
      N.le_trans(Nat.add(l1, l2), x, Nat.max(1n, x),
        AB.subst(Nat, z => {Nat.is_le(Nat.add(l1, l2), z) == True{} : Bool}, Nat.add(h, Nat.sub(x, h)), x, half_rest(x, hx1), add_le2(l1, h, l2, Nat.sub(x, h), i1, i2)),
        le_max_r1(x))

# A read that does not fit is asked in two halves: at least two reads.
def pl2(+f: Nat, +c: String, +a: Nat, +b: Nat) -> {Nat.is_le(2n, PGL(1n+f, False{}, c, a, b)) == True{} : Bool}:
  +m = PM(a, b)
  +xs = Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m)
  +ys = Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b)
  %Equal.sym(Nat, List.length(&2, Pr.Req, List.append(&2, Pr.Req, xs, ys)), Nat.add(List.length(&2, Pr.Req, xs), List.length(&2, Pr.Req, ys)), len_app(xs, ys)) : {Nat.is_le(2n, _) == True{} : Bool}
  add_le2(1n, List.length(&2, Pr.Req, xs), 1n, List.length(&2, Pr.Req, ys), pl1(f, Norm.le31(Nat.sub(m, a)), c, a, m), pl1(f, Norm.le31(Nat.sub(b, m)), c, m, b))

def str_assoc(+a: String, +b: String, +c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %str_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}
