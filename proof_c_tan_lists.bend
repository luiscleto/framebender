import Base
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import lawful-bytes@0.1.0.0/proof_seq.bend as BQ
import lawful-bytes@0.1.0.0/proof_same.bend as BS
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# Phase C, area "tan": lemmas on lists of bytes, on Q.BF (bytes to bases),
# on numbers and words, and NX.code against B.Base.of_fasta.

# ---------------------------------------------------------------------------
# Bool and Nat
# ---------------------------------------------------------------------------

law lt_zero_t:
  for +i: Nat
  for +h: {Nat.is_lt(i, 0n) == True{} : Bool}
  Empty

def lt_zero_t(i, h):
  N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, N.lt_zero(i)), h))

law and_l:
  for +a: Bool
  for +b: Bool
  for +h: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_l(a, b, h):
  N.and_true_l(a, b, h)

law and_r:
  for +a: Bool
  for +b: Bool
  for +h: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_r(a, b, h):
  N.and_true_r(a, b, h)

law and_tt:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_tt(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

law and_assoc:
  for a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}

def and_assoc(a, b, c):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law sub_sub:
  for a: Nat
  for b: Nat
  for +c: Nat
  {Nat.sub(Nat.sub(a, b), c) == Nat.sub(a, Nat.add(b, c)) : Nat}

def sub_sub(a, b, c):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, c)

# (a + j) - c = (a - c) + j when c <= a.
law add_sub_r:
  for a: Nat
  for c: Nat
  for +j: Nat
  for +h: {Nat.is_le(c, a) == True{} : Bool}
  {Nat.sub(Nat.add(a, j), c) == Nat.add(Nat.sub(a, c), j) : Nat}

def add_sub_r(a, c, j, h):
  match a c:
    case 0n 0n:
      N.sub_zero(j)
    case 0n 1n+q:
      Empty.absurd({Nat.sub(j, 1n+q) == j : Nat}, N.false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      add_sub_r(p, q, j, h)

# a - b + b = a when b <= a.
law sub_add_id:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(b, a) == True{} : Bool}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

def sub_add_id(a, b, h):
  %N.add_comm(b, Nat.sub(a, b)) : {_ == a : Nat}
  N.le_sub_add(b, a, h)

# a + c <= b gives c <= b - a.
law le_sub:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for +h: {Nat.is_le(Nat.add(a, c), b) == True{} : Bool}
  {Nat.is_le(c, Nat.sub(b, a)) == True{} : Bool}

def le_sub(a, c, b, h):
  N.le_sub_r(a, c, b, h)

# c <= b - a gives a + c <= b, when a <= b.
law sub_le_add:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for +hab: {Nat.is_le(a, b) == True{} : Bool}
  for +h: {Nat.is_le(c, Nat.sub(b, a)) == True{} : Bool}
  {Nat.is_le(Nat.add(a, c), b) == True{} : Bool}

def sub_le_add(a, c, b, hab, h):
  %N.le_sub_add(a, b, hab) : {Nat.is_le(Nat.add(a, c), _) == True{} : Bool}
  N.le_add_mono_l(a, c, Nat.sub(b, a), h)

law le_of_lt:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def le_of_lt(a, b, h):
  N.lt_to_le(a, b, h)

# a < b is a + 1 <= b.
law lt_succ_le:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(Nat.add(a, 1n), b) == True{} : Bool}

def lt_succ_le(a, b, h):
  %Equal.sym(Nat, Nat.add(a, 1n), 1n+a, N.add_one(a)) : {Nat.is_le(_, b) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(1n+a, b), Nat.is_lt(a, b), N.le_succ_lt(a, b)) : {_ == True{} : Bool}
  h

law le_succ_lt:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(Nat.add(a, 1n), b) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

def le_succ_lt(a, b, h):
  %N.le_succ_lt(a, b) : {_ == True{} : Bool}
  %N.add_one(a) : {Nat.is_le(_, b) == True{} : Bool}
  h

# ---------------------------------------------------------------------------
# Words
# ---------------------------------------------------------------------------

law u_sub:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}
  {U32.to_nat((a - b : U32)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

def u_sub(a, b, h):
  U.to_nat_sub_le(a, b, Equal.trans(Bool, U32.is_le(b, a), Nat.is_le(U32.to_nat(b), U32.to_nat(a)), True{}, U.is_le_to_nat(b, a), h))

# A sum that stays within a word c does not wrap.
law u_add:
  for +a: U32
  for +b: U32
  for +c: U32
  for +h: {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat((a + b : U32)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

def u_add(a, b, c, h):
  U.to_nat_add_fits_p(a, b, N.le_lt_trans(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c), Nat.pow(2n, 32n), h, U.to_nat_lt_p(c)))

law u_inc:
  for +a: U32
  for +c: U32
  for +h: {Nat.is_lt(U32.to_nat(a), U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat((a + 1 : U32)) == Nat.add(U32.to_nat(a), 1n) : Nat}

def u_inc(a, c, h):
  u_add(a, 1, c, lt_succ_le(U32.to_nat(a), U32.to_nat(c), h))

law u_from:
  for +d: Nat
  for +c: U32
  for +h: {Nat.is_lt(d, U32.to_nat(c)) == True{} : Bool}
  {U32.to_nat(U32.from_nat(d)) == d : Nat}

def u_from(d, c, h):
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(d)), Nat.mod(d, Nat.pow(2n, 32n)), U.to_nat_from_nat_p(d)) : {_ == d : Nat}
  N.mod_small(d, Nat.pow(2n, 32n), N.lt_trans(d, U32.to_nat(c), Nat.pow(2n, 32n), h, U.to_nat_lt_p(c)))

law u_le:
  for +a: U32
  for +b: U32
  {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u_le(a, b):
  U.is_le_to_nat(a, b)

# ---------------------------------------------------------------------------
# Lists of bytes
# ---------------------------------------------------------------------------

law get_app_l:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for i: Nat
  for +h: {Nat.is_lt(i, List.length(&2, U32, xs)) == True{} : Bool}
  {List.get(&2, U32, List.append(&2, U32, xs, ys), i) == List.get(&2, U32, xs, i) : Maybe<&2, U32>}

def get_app_l(xs, ys, i, h):
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, U32, ys, i) == None{} : Maybe<&2, U32>}, lt_zero_t(i, h))
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      get_app_l(t, ys, p, h)

law get_app_r:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +i: Nat
  {List.get(&2, U32, List.append(&2, U32, xs, ys), Nat.add(List.length(&2, U32, xs), i)) == List.get(&2, U32, ys, i) : Maybe<&2, U32>}

def get_app_r(xs, ys, i):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      get_app_r(t, ys, i)

law get_take:
  for xs: List<&2, U32>
  for m: Nat
  for i: Nat
  for +h: {Nat.is_lt(i, m) == True{} : Bool}
  {List.get(&2, U32, List.take(&2, U32, xs, m), i) == List.get(&2, U32, xs, i) : Maybe<&2, U32>}

def get_take(xs, m, i, h):
  match xs m i:
    case Nil{} _ _:
      {==}
    case x <> t 0n _:
      Empty.absurd({None{} == List.get(&2, U32, x <> t, i) : Maybe<&2, U32>}, lt_zero_t(i, h))
    case x <> t 1n+q 0n:
      {==}
    case x <> t 1n+q 1n+p:
      get_take(t, q, p, h)

law get_drop:
  for xs: List<&2, U32>
  for s: Nat
  for +i: Nat
  {List.get(&2, U32, List.drop(&2, U32, xs, s), i) == List.get(&2, U32, xs, Nat.add(s, i)) : Maybe<&2, U32>}

def get_drop(xs, s, i):
  match xs s:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      get_drop(t, p, i)

law len_drop:
  for xs: List<&2, U32>
  for d: Nat
  {List.length(&2, U32, List.drop(&2, U32, xs, d)) == Nat.sub(List.length(&2, U32, xs), d) : Nat}

def len_drop(xs, d):
  match xs d:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      len_drop(t, p)

law len_app:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}

def len_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, t, ys)), Nat.add(List.length(&2, U32, t), List.length(&2, U32, ys)), len_app(t, ys)) :
        {1n+_ == 1n+Nat.add(List.length(&2, U32, t), List.length(&2, U32, ys)) : Nat}
      {==}

law len_take:
  for +xs: List<&2, U32>
  for +m: Nat
  for +h: {Nat.is_le(m, List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, List.take(&2, U32, xs, m)) == m : Nat}

def len_take(xs, m, h):
  BQ.take_length(xs, m, h)

law take_take:
  for +xs: List<&2, U32>
  for +m: Nat
  for +n: Nat
  for +h: {Nat.is_le(n, m) == True{} : Bool}
  {List.take(&2, U32, List.take(&2, U32, xs, m), n) == List.take(&2, U32, xs, n) : List<&2, U32>}

def take_take(xs, m, n, h):
  BQ.take_take(xs, m, n, h)

law drop_zero:
  for +xs: List<&2, U32>
  {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}

def drop_zero(xs):
  BS.drop_zero(xs)

law slice_cons:
  for +xs: List<&2, U32>
  for +j: Nat
  for +k: Nat
  for +x: U32
  for +h: {List.get(&2, U32, xs, j) == Some{x} : Maybe<&2, U32>}
  {List.take(&2, U32, List.drop(&2, U32, xs, j), 1n+k) == x <> List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(j, 1n)), k) : List<&2, U32>}

def slice_cons(xs, j, k, x, h):
  BS.slice_cons(xs, j, k, x, h)

# The last of the first i + 1 is element i.
law last_take:
  for xs: List<&2, U32>
  for i: Nat
  for +h: {Nat.is_lt(i, List.length(&2, U32, xs)) == True{} : Bool}
  {List.last(&2, U32, List.take(&2, U32, xs, 1n+i)) == List.get(&2, U32, xs, i) : Maybe<&2, U32>}

def last_take(xs, i, h):
  match xs:
    case Nil{}:
      Empty.absurd({None{} == None{} : Maybe<&2, U32>}, lt_zero_t(i, h))
    case x <> t:
      match t i:
        case Nil{} 0n:
          {==}
        case Nil{} 1n+p:
          Empty.absurd({Some{x} == None{} : Maybe<&2, U32>}, lt_zero_t(p, h))
        case y <> u 0n:
          {==}
        case y <> u 1n+p:
          last_take(y <> u, p, h)

law head_drop:
  for xs: List<&2, U32>
  for d: Nat
  {List.head(&2, U32, List.drop(&2, U32, xs, d)) == List.get(&2, U32, xs, d) : Maybe<&2, U32>}

def head_drop(xs, d):
  match xs d:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      head_drop(t, p)

law tail_drop:
  for xs: List<&2, U32>
  for d: Nat
  {List.tail(&2, U32, List.drop(&2, U32, xs, d)) == List.drop(&2, U32, xs, 1n+d) : List<&2, U32>}

def tail_drop(xs, d):
  match xs d:
    case Nil{} _:
      {==}
    case x <> t 0n:
      Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, BS.drop_zero(t))
    case x <> t 1n+p:
      tail_drop(t, p)

# ---------------------------------------------------------------------------
# Bytes to bases
# ---------------------------------------------------------------------------

def MB(m: Maybe<&2, U32>) -> Maybe<&2, B.Base>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{Q.bf(x)}

law bf_len:
  for xs: List<&2, U32>
  {List.length(&2, B.Base, Q.BF(xs)) == List.length(&2, U32, xs) : Nat}

def bf_len(xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Nat, List.length(&2, B.Base, Q.BF(t)), List.length(&2, U32, t), bf_len(t)) :
        {1n+_ == 1n+List.length(&2, U32, t) : Nat}
      {==}

law bf_take:
  for xs: List<&2, U32>
  for m: Nat
  {Q.BF(List.take(&2, U32, xs, m)) == List.take(&2, B.Base, Q.BF(xs), m) : List<&2, B.Base>}

def bf_take(xs, m):
  match xs m:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case +x <> t 1n+p:
      %Equal.sym(List<&2, B.Base>, Q.BF(List.take(&2, U32, t, p)), List.take(&2, B.Base, Q.BF(t), p), bf_take(t, p)) :
        {Q.bf(x) <> _ == Q.bf(x) <> List.take(&2, B.Base, Q.BF(t), p) : List<&2, B.Base>}
      {==}

law bf_last_go:
  for t: List<&2, U32>
  for h: U32
  {List.last.go(&2, B.Base, Q.BF(t), Q.bf(h)) == Q.bf(List.last.go(&2, U32, t, h)) : B.Base}

def bf_last_go(t, h):
  match t:
    case Nil{}:
      {==}
    case y <> u:
      bf_last_go(u, y)

law bf_last:
  for xs: List<&2, U32>
  {List.last(&2, B.Base, Q.BF(xs)) == MB(List.last(&2, U32, xs)) : Maybe<&2, B.Base>}

def bf_last(xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(B.Base, List.last.go(&2, B.Base, Q.BF(t), Q.bf(x)), Q.bf(List.last.go(&2, U32, t, x)), bf_last_go(t, x)) :
        {Some{_} == Some{Q.bf(List.last.go(&2, U32, t, x))} : Maybe<&2, B.Base>}
      {==}

law bf_head:
  for xs: List<&2, U32>
  {List.head(&2, B.Base, Q.BF(xs)) == MB(List.head(&2, U32, xs)) : Maybe<&2, B.Base>}

def bf_head(xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

law bf_tail:
  for xs: List<&2, U32>
  {List.tail(&2, B.Base, Q.BF(xs)) == Q.BF(List.tail(&2, U32, xs)) : List<&2, B.Base>}

def bf_tail(xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

law bf_get:
  for xs: List<&2, U32>
  for i: Nat
  {List.get(&2, B.Base, Q.BF(xs), i) == MB(List.get(&2, U32, xs, i)) : Maybe<&2, B.Base>}

def bf_get(xs, i):
  match xs i:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      bf_get(t, p)

# ---------------------------------------------------------------------------
# NX.code is B.Base.of_fasta's base, as a number
# ---------------------------------------------------------------------------

def bidx(b: B.Base) -> U32:
  match b:
    case B.A{}:
      0
    case B.C{}:
      1
    case B.G{}:
      2
    case B.T{}:
      3
    case B.N{}:
      4

law pick_idx:
  for c1: Bool
  for c2: Bool
  for c3: Bool
  for c4: Bool
  {bidx(B.Base.when(c1, B.A{}, B.Base.when(c2, B.C{}, B.Base.when(c3, B.G{}, B.Base.when(c4, B.T{}, B.N{}))))) == Bool.pick(U32, c1, 0, Bool.pick(U32, c2, 1, Bool.pick(U32, c3, 2, Bool.pick(U32, c4, 3, 4)))) : U32}

def pick_idx(c1, c2, c3, c4):
  match c1 c2 c3 c4:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} True{} _:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

law code_idx:
  for +x: U32
  {bidx(Q.bf(x)) == NX.code(x) : U32}

def code_idx(x):
  +u = B.Char.code(Char.to_upper(Chr{x}))
  pick_idx(U32.is_eq(u, 65) || U32.is_eq(u, 82) || U32.is_eq(u, 77) || U32.is_eq(u, 87) || U32.is_eq(u, 68) || U32.is_eq(u, 72) || U32.is_eq(u, 86),
    U32.is_eq(u, 67) || U32.is_eq(u, 89) || U32.is_eq(u, 83) || U32.is_eq(u, 66),
    U32.is_eq(u, 71) || U32.is_eq(u, 75),
    U32.is_eq(u, 84))

law beq_idx:
  for a: B.Base
  for b: B.Base
  {B.Base.is_eq(a, b) == U32.is_eq(bidx(b), bidx(a)) : Bool}

def beq_idx(a, b):
  match a b:
    case B.A{} B.A{}:
      {==}
    case B.A{} B.C{}:
      {==}
    case B.A{} B.G{}:
      {==}
    case B.A{} B.T{}:
      {==}
    case B.A{} B.N{}:
      {==}
    case B.C{} B.A{}:
      {==}
    case B.C{} B.C{}:
      {==}
    case B.C{} B.G{}:
      {==}
    case B.C{} B.T{}:
      {==}
    case B.C{} B.N{}:
      {==}
    case B.G{} B.A{}:
      {==}
    case B.G{} B.C{}:
      {==}
    case B.G{} B.G{}:
      {==}
    case B.G{} B.T{}:
      {==}
    case B.G{} B.N{}:
      {==}
    case B.T{} B.A{}:
      {==}
    case B.T{} B.C{}:
      {==}
    case B.T{} B.G{}:
      {==}
    case B.T{} B.T{}:
      {==}
    case B.T{} B.N{}:
      {==}
    case B.N{} B.A{}:
      {==}
    case B.N{} B.C{}:
      {==}
    case B.N{} B.G{}:
      {==}
    case B.N{} B.T{}:
      {==}
    case B.N{} B.N{}:
      {==}

# Two bytes' bases are equal iff their codes are.
law beq_code:
  for +x: U32
  for +y: U32
  {B.Base.is_eq(Q.bf(x), Q.bf(y)) == U32.is_eq(NX.code(y), NX.code(x)) : Bool}

def beq_code(x, y):
  %code_idx(y) : {B.Base.is_eq(Q.bf(x), Q.bf(y)) == U32.is_eq(_, NX.code(x)) : Bool}
  %code_idx(x) : {B.Base.is_eq(Q.bf(x), Q.bf(y)) == U32.is_eq(bidx(Q.bf(y)), _) : Bool}
  beq_idx(Q.bf(x), Q.bf(y))
