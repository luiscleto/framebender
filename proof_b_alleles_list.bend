import Base
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_seq.bend as Q
import lawful-bytes@0.1.1.0/proof_list.bend as BL
import lawful-bytes@0.1.1.0/proof_same.bend as S
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-fields@0.1.1.0/defs.bend as FD

# List facts for proof_b_alleles.bend: FD.split at the first separator, and
# take/drop/slice arithmetic. Every variable is reusable.
#
# Rewrites: `%e : G` with e : {new == old}; G is the goal with `_` where old
# is.

def L32() -> Data:
  List<&2, U32>

def LL() -> Data:
  List<&2, List<&2, U32>>

def take(xs: L32(), +n: Nat) -> L32():
  List.take(&2, U32, xs, n)

def drop(xs: L32(), +n: Nat) -> L32():
  List.drop(&2, U32, xs, n)

def lapp(xs: LL(), ys: LL()) -> LL():
  List.append(&2, List<&2, U32>, xs, ys)

# Bool
# ====

def bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law ft:
  for e: {False{} == True{} : Bool}
  Empty

def ft(e):
  %e : bdisc(_)
  Unit{}

law and_l:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ft(e))

law and_r:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, ft(e))

law not_t:
  for +a: Bool
  for +e: {Bool.not(a) == True{} : Bool}
  {a == False{} : Bool}

def not_t(a, e):
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, ft(e))

law and_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}

def and_assoc(a, b, c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law and_true:
  for +a: Bool
  {Bool.and(a, True{}) == a : Bool}

def and_true(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# Splitting at the first separator
# ================================

# The pieces after the first separator of zs (zs is empty or starts with it).
def tsplit(zs: L32(), +sep: U32) -> LL():
  match zs:
    case Nil{}:
      Nil{}
    case Con{z, t}:
      FD.split(t, sep)

def SRn(+ys: L32(), +sep: U32, +r: Nat) -> LL():
  Con{take(ys, r), tsplit(drop(ys, r), sep)}

def SR(+ys: L32(), +sep: U32) -> LL():
  SRn(ys, sep, D.run_len(ys, sep))

def split_run.k(+y: U32, +t: L32(), +sep: U32, +b: Bool, +ih: {FD.split(t, sep) == SR(t, sep) : LL()}) ->
  {FD.split.fin(y, FD.split(t, sep), b) == SRn(y <> t, sep, Bool.pick(Nat, b, 0n, Nat.add(1n, D.run_len(t, sep)))) : LL()}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(LL(), FD.split(t, sep), SR(t, sep), ih) : {FD.split.push(y, _) == SRn(y <> t, sep, 1n+D.run_len(t, sep)) : LL()}
      {==}

# The first piece of ys is its run before the first separator; the rest are
# the pieces after it.
law split_run:
  for +ys: L32()
  for +sep: U32
  {FD.split(ys, sep) == SR(ys, sep) : LL()}

def split_run(ys, sep):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      split_run.k(y, t, sep, U32.is_eq(y, sep), split_run(t, sep))

def split_one.k(+y: U32, +t: L32(), +sep: U32, +b: Bool, +e: {U32.is_eq(y, sep) == b : Bool},
  +ih: {FD.split(take(t, D.run_len(t, sep)), sep) == [take(t, D.run_len(t, sep))] : LL()}) ->
  {FD.split(take(y <> t, Bool.pick(Nat, b, 0n, Nat.add(1n, D.run_len(t, sep)))), sep) == [take(y <> t, Bool.pick(Nat, b, 0n, Nat.add(1n, D.run_len(t, sep))))] : LL()}:
  match b:
    case True{}:
      {==}
    case False{}:
      +T = take(t, D.run_len(t, sep))
      %Equal.sym(Bool, U32.is_eq(y, sep), False{}, e) : {FD.split.fin(y, FD.split(T, sep), _) == [y <> T] : LL()}
      %Equal.sym(LL(), FD.split(T, sep), [T], ih) : {FD.split.push(y, _) == [y <> T] : LL()}
      {==}

# The run before the first separator is one piece.
law split_one:
  for +ys: L32()
  for +sep: U32
  {FD.split(take(ys, D.run_len(ys, sep)), sep) == [take(ys, D.run_len(ys, sep))] : LL()}

def split_one(ys, sep):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      split_one.k(y, t, sep, U32.is_eq(y, sep), {==}, split_one(t, sep))

def split_app.k(+u: U32, +t: L32(), +V: LL(), +sep: U32, +b: Bool) ->
  {FD.split.fin(u, lapp(FD.split(t, sep), V), b) == lapp(FD.split.fin(u, FD.split(t, sep), b), V) : LL()}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(LL(), FD.split(t, sep), SR(t, sep), split_run(t, sep)) :
        {FD.split.push(u, lapp(_, V)) == lapp(FD.split.push(u, _), V) : LL()}
      {==}

# Splitting us, a separator, vs: the pieces of us then those of vs.
law split_app:
  for +us: L32()
  for +vs: L32()
  for +sep: U32
  {FD.split(List.append(&2, U32, us, sep <> vs), sep) == lapp(FD.split(us, sep), FD.split(vs, sep)) : LL()}

def split_app(us, vs, sep):
  match us:
    case Nil{}:
      %Equal.sym(Bool, U32.is_eq(sep, sep), True{}, BL.pl_u32_eq_refl(sep)) :
        {FD.split.fin(sep, FD.split(vs, sep), _) == Nil{} <> FD.split(vs, sep) : LL()}
      {==}
    case Con{+u, +t}:
      %Equal.sym(LL(), FD.split(List.append(&2, U32, t, sep <> vs), sep), lapp(FD.split(t, sep), FD.split(vs, sep)), split_app(t, vs, sep)) :
        {FD.split.fin(u, _, U32.is_eq(u, sep)) == lapp(FD.split(u <> t, sep), FD.split(vs, sep)) : LL()}
      split_app.k(u, t, FD.split(vs, sep), sep, U32.is_eq(u, sep))

# take and drop
# =============

law drop_take:
  for +xs: L32()
  for +m: Nat
  for +r: Nat
  {drop(take(xs, m), r) == take(drop(xs, r), Nat.sub(m, r)) : L32()}

def drop_take(xs, m, r):
  match xs m r:
    case Nil{} _ _:
      {==}
    case Con{+x, +t} 0n _:
      Equal.sym(L32(), take(drop(x <> t, r), 0n), Nil{}, Q.take_zero(drop(x <> t, r)))
    case Con{+x, +t} 1n+p 0n:
      {==}
    case Con{+x, +t} 1n+p 1n+q:
      drop_take(t, p, q)

law drop_drop:
  for +xs: L32()
  for +a: Nat
  for +r: Nat
  {drop(drop(xs, a), r) == drop(xs, Nat.add(a, r)) : L32()}

def drop_drop(xs, a, r):
  match xs a:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      drop_drop(t, p, r)

law take_add:
  for +xs: L32()
  for +m1: Nat
  for +m2: Nat
  {take(xs, Nat.add(m1, m2)) == List.append(&2, U32, take(xs, m1), take(drop(xs, m1), m2)) : L32()}

def take_add(xs, m1, m2):
  match xs m1:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      %take_add(t, p, m2) : {x <> take(t, Nat.add(p, m2)) == x <> _ : L32()}
      {==}

# Nat
# ===

law sub_sub:
  for +e: Nat
  for +a: Nat
  for +r: Nat
  {Nat.sub(Nat.sub(e, a), r) == Nat.sub(e, Nat.add(a, r)) : Nat}

def sub_sub(e, a, r):
  match e a:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, r)

law sub_self:
  for +e: Nat
  {Nat.sub(e, e) == 0n : Nat}

def sub_self(e):
  match e:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# c < e: e - c is 1 + (e - (c + 1)).
law sub_lt:
  for +e: Nat
  for +c: Nat
  for +h: {Nat.is_lt(c, e) == True{} : Bool}
  {Nat.sub(e, c) == 1n+Nat.sub(e, Nat.add(c, 1n)) : Nat}

def sub_lt(e, c, h):
  match e c:
    case 0n _:
      Empty.absurd({0n == 1n+Nat.sub(0n, Nat.add(c, 1n)) : Nat}, ft(Equal.trans(Bool, False{}, Nat.is_lt(c, 0n), True{}, Equal.sym(Bool, Nat.is_lt(c, 0n), False{}, N.lt_zero(c)), h)))
    case 1n+p 0n:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {1n+p == 1n+_ : Nat}
      {==}
    case 1n+p 1n+q:
      sub_lt(p, q, h)

# i <= j <= k: (j - i) + (k - j) is k - i.
law sub_split:
  for +i: Nat
  for +j: Nat
  for +k: Nat
  for +hij: {Nat.is_le(i, j) == True{} : Bool}
  for +hjk: {Nat.is_le(j, k) == True{} : Bool}
  {Nat.add(Nat.sub(j, i), Nat.sub(k, j)) == Nat.sub(k, i) : Nat}

def sub_split(i, j, k, hij, hjk):
  +x = Nat.sub(j, i)
  +y = Nat.sub(k, j)
  +ek = Equal.trans(Nat, Nat.add(i, Nat.add(x, y)), Nat.add(Nat.add(i, x), y), k,
    Equal.sym(Nat, Nat.add(Nat.add(i, x), y), Nat.add(i, Nat.add(x, y)), N.add_assoc(i, x, y)),
    %Equal.sym(Nat, Nat.add(i, x), j, N.le_sub_add(i, j, hij)) : {Nat.add(_, y) == k : Nat}; N.le_sub_add(j, k, hjk))
  %ek : {Nat.add(x, y) == Nat.sub(_, i) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(i, Nat.add(x, y)), i), Nat.add(x, y), N.sub_add_l(i, Nat.add(x, y)))

# Slices of one list, at Nat positions
# ====================================

law slice_app:
  for +X: L32()
  for +i: Nat
  for +j: Nat
  for +k: Nat
  for +hij: {Nat.is_le(i, j) == True{} : Bool}
  for +hjk: {Nat.is_le(j, k) == True{} : Bool}
  {D.slice(X, i, Nat.sub(k, i)) == List.append(&2, U32, D.slice(X, i, Nat.sub(j, i)), D.slice(X, j, Nat.sub(k, j))) : L32()}

def slice_app(X, i, j, k, hij, hjk):
  +x = Nat.sub(j, i)
  +y = Nat.sub(k, j)
  %sub_split(i, j, k, hij, hjk) : {take(drop(X, i), _) == List.append(&2, U32, D.slice(X, i, x), D.slice(X, j, y)) : L32()}
  %Equal.sym(L32(), take(drop(X, i), Nat.add(x, y)), List.append(&2, U32, take(drop(X, i), x), take(drop(drop(X, i), x), y)), take_add(drop(X, i), x, y)) :
    {_ == List.append(&2, U32, D.slice(X, i, x), D.slice(X, j, y)) : L32()}
  %Equal.sym(L32(), drop(drop(X, i), x), drop(X, Nat.add(i, x)), drop_drop(X, i, x)) :
    {List.append(&2, U32, take(drop(X, i), x), take(_, y)) == List.append(&2, U32, D.slice(X, i, x), D.slice(X, j, y)) : L32()}
  %Equal.sym(Nat, Nat.add(i, x), j, N.le_sub_add(i, j, hij)) :
    {List.append(&2, U32, take(drop(X, i), x), take(drop(X, _), y)) == List.append(&2, U32, D.slice(X, i, x), D.slice(X, j, y)) : L32()}
  {==}

# The first piece of a slice ends at the first separator (first); the rest
# are the pieces after it.
law spl:
  for +X: L32()
  for +a: Nat
  for +e: Nat
  for +sep: U32
  {FD.split(D.slice(X, a, Nat.sub(e, a)), sep) == Con{D.slice(X, a, Nat.sub(D.first(X, a, e, sep), a)), tsplit(D.slice(X, D.first(X, a, e, sep), Nat.sub(e, D.first(X, a, e, sep))), sep)} : LL()}

def spl(X, a, e, sep):
  +L = drop(X, a)
  +m = Nat.sub(e, a)
  +ys = take(L, m)
  +r = D.run_len(ys, sep)
  +c = Nat.add(a, r)
  +RHS = {Con{D.slice(X, a, Nat.sub(c, a)), tsplit(D.slice(X, c, Nat.sub(e, c)), sep)} : LL()}
  %Equal.sym(LL(), FD.split(ys, sep), SR(ys, sep), split_run(ys, sep)) : {_ == RHS : LL()}
  %Equal.sym(L32(), take(take(L, m), r), take(L, r), Q.take_take(L, m, r, BL.pl_r_le(L, m, sep))) :
    {Con{_, tsplit(drop(ys, r), sep)} == RHS : LL()}
  %Equal.sym(L32(), drop(take(L, m), r), take(drop(L, r), Nat.sub(m, r)), drop_take(L, m, r)) :
    {Con{take(L, r), tsplit(_, sep)} == RHS : LL()}
  %Equal.sym(L32(), drop(drop(X, a), r), drop(X, c), drop_drop(X, a, r)) :
    {Con{take(L, r), tsplit(take(_, Nat.sub(m, r)), sep)} == RHS : LL()}
  %Equal.sym(Nat, Nat.sub(Nat.sub(e, a), r), Nat.sub(e, c), sub_sub(e, a, r)) :
    {Con{take(L, r), tsplit(take(drop(X, c), _), sep)} == RHS : LL()}
  %Equal.sym(Nat, Nat.sub(c, a), r, N.sub_add_l(a, r)) :
    {Con{take(L, r), tsplit(D.slice(X, c, Nat.sub(e, c)), sep)} == Con{take(L, _), tsplit(D.slice(X, c, Nat.sub(e, c)), sep)} : LL()}
  {==}

law ts_eq:
  for +X: L32()
  for +e: Nat
  for +sep: U32
  {tsplit(D.slice(X, e, Nat.sub(e, e)), sep) == Nil{} : LL()}

def ts_eq(X, e, sep):
  %Equal.sym(Nat, Nat.sub(e, e), 0n, sub_self(e)) : {tsplit(take(drop(X, e), _), sep) == Nil{} : LL()}
  %Equal.sym(L32(), take(drop(X, e), 0n), Nil{}, Q.take_zero(drop(X, e))) : {tsplit(_, sep) == Nil{} : LL()}
  {==}

law slice_lt:
  for +X: L32()
  for +c: Nat
  for +e: Nat
  for +y: U32
  for +h: {Nat.is_lt(c, e) == True{} : Bool}
  for +hg: {List.get(&2, U32, X, c) == Some{y} : Maybe<&2, U32>}
  {D.slice(X, c, Nat.sub(e, c)) == y <> D.slice(X, Nat.add(c, 1n), Nat.sub(e, Nat.add(c, 1n))) : L32()}

def slice_lt(X, c, e, y, h, hg):
  %Equal.sym(Nat, Nat.sub(e, c), 1n+Nat.sub(e, Nat.add(c, 1n)), sub_lt(e, c, h)) :
    {D.slice(X, c, _) == y <> D.slice(X, Nat.add(c, 1n), Nat.sub(e, Nat.add(c, 1n))) : L32()}
  S.slice_cons(X, c, Nat.sub(e, Nat.add(c, 1n)), y, hg)

law ts_lt:
  for +X: L32()
  for +c: Nat
  for +e: Nat
  for +sep: U32
  for +h: {Nat.is_lt(c, e) == True{} : Bool}
  for +hg: {List.get(&2, U32, X, c) == Some{sep} : Maybe<&2, U32>}
  {tsplit(D.slice(X, c, Nat.sub(e, c)), sep) == FD.split(D.slice(X, Nat.add(c, 1n), Nat.sub(e, Nat.add(c, 1n))), sep) : LL()}

def ts_lt(X, c, e, sep, h, hg):
  %Equal.sym(L32(), D.slice(X, c, Nat.sub(e, c)), sep <> D.slice(X, Nat.add(c, 1n), Nat.sub(e, Nat.add(c, 1n))), slice_lt(X, c, e, sep, h, hg)) :
    {tsplit(_, sep) == FD.split(D.slice(X, Nat.add(c, 1n), Nat.sub(e, Nat.add(c, 1n))), sep) : LL()}
  {==}

# The first piece has no separator: it splits into itself.
law one:
  for +X: L32()
  for +a: Nat
  for +e: Nat
  for +sep: U32
  {FD.split(D.slice(X, a, Nat.sub(D.first(X, a, e, sep), a)), sep) == [D.slice(X, a, Nat.sub(D.first(X, a, e, sep), a))] : LL()}

def one(X, a, e, sep):
  +L = drop(X, a)
  +m = Nat.sub(e, a)
  +ys = take(L, m)
  +r = D.run_len(ys, sep)
  %Equal.sym(Nat, Nat.sub(Nat.add(a, r), a), r, N.sub_add_l(a, r)) : {FD.split(take(L, _), sep) == [take(L, _)] : LL()}
  %Q.take_take(L, m, r, BL.pl_r_le(L, m, sep)) : {FD.split(_, sep) == [_] : LL()}
  split_one(ys, sep)

law lt_first:
  for +p: Nat
  for +r: Nat
  {Nat.is_lt(p, Nat.add(Nat.add(p, 1n), r)) == True{} : Bool}

def lt_first(p, r):
  %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, N.add_one(p)) : {Nat.is_lt(p, Nat.add(_, r)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(p, 1n+Nat.add(p, r)), Nat.is_le(p, Nat.add(p, r)), N.lt_succ_iff(p, Nat.add(p, r))) : {_ == True{} : Bool}
  N.le_add_r(p, r)

# The earlier pieces grow by one: s .. p-1, the separator at p, then the
# first piece from p + 1.
law ext:
  for +X: L32()
  for +s: Nat
  for +p: Nat
  for +e: Nat
  for +sep: U32
  for +hs: {Nat.is_le(s, p) == True{} : Bool}
  for +hg: {List.get(&2, U32, X, p) == Some{sep} : Maybe<&2, U32>}
  {FD.split(D.slice(X, s, Nat.sub(D.first(X, Nat.add(p, 1n), e, sep), s)), sep) == lapp(FD.split(D.slice(X, s, Nat.sub(p, s)), sep), [D.slice(X, Nat.add(p, 1n), Nat.sub(D.first(X, Nat.add(p, 1n), e, sep), Nat.add(p, 1n)))]) : LL()}

def ext(X, s, p, e, sep, hs, hg):
  +a = Nat.add(p, 1n)
  +c = D.first(X, a, e, sep)
  +hpc = lt_first(p, D.run_len(D.slice(X, a, Nat.sub(e, a)), sep))
  +Q1 = D.slice(X, a, Nat.sub(c, a))
  %Equal.sym(L32(), D.slice(X, s, Nat.sub(c, s)), List.append(&2, U32, D.slice(X, s, Nat.sub(p, s)), D.slice(X, p, Nat.sub(c, p))), slice_app(X, s, p, c, hs, N.lt_to_le(p, c, hpc))) :
    {FD.split(_, sep) == lapp(FD.split(D.slice(X, s, Nat.sub(p, s)), sep), [Q1]) : LL()}
  %Equal.sym(L32(), D.slice(X, p, Nat.sub(c, p)), sep <> Q1, slice_lt(X, p, c, sep, hpc, hg)) :
    {FD.split(List.append(&2, U32, D.slice(X, s, Nat.sub(p, s)), _), sep) == lapp(FD.split(D.slice(X, s, Nat.sub(p, s)), sep), [Q1]) : LL()}
  %Equal.sym(LL(), FD.split(List.append(&2, U32, D.slice(X, s, Nat.sub(p, s)), sep <> Q1), sep), lapp(FD.split(D.slice(X, s, Nat.sub(p, s)), sep), FD.split(Q1, sep)), split_app(D.slice(X, s, Nat.sub(p, s)), Q1, sep)) :
    {_ == lapp(FD.split(D.slice(X, s, Nat.sub(p, s)), sep), [Q1]) : LL()}
  %Equal.sym(LL(), FD.split(Q1, sep), [Q1], one(X, a, e, sep)) :
    {lapp(FD.split(D.slice(X, s, Nat.sub(p, s)), sep), _) == lapp(FD.split(D.slice(X, s, Nat.sub(p, s)), sep), [Q1]) : LL()}
  {==}
