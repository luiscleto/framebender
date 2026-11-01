import Base
import ./norm_fast.bend as NF
import ./proof_b_cut_pair.bend as M
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_find.bend as PF
import lawful-bytes@0.1.1.0/proof_list.bend as PL
import lawful-bytes@0.1.1.0/proof_ops.bend as PO
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The searches of the cut as facts about the view: each field end is the
# first tab or LF from the field's start, below len, and a tab; LF searches
# skip tabs; the first tab of a range.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def X(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

# ---------------------------------------------------------------------------
# Small facts
# ---------------------------------------------------------------------------

def vlen(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {List.length(&2, U32, X(len, t)) == n(len) : Nat}:
  PO.view_size_t(len, t, d, hok)

def le_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h: {Nat.is_le(x, n(len)) == True{} : Bool}) -> {Nat.is_le(x, List.length(&2, U32, X(len, t))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, X(len, t)), n(len), vlen(len, t, d, hok)) : {Nat.is_le(x, _) == True{} : Bool}
  h

def ule(+a: U32, +b: U32, +h: {U32.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(n(a), n(b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(n(a), n(b)), U32.is_le(a, b), True{}, Equal.sym(Bool, U32.is_le(a, b), Nat.is_le(n(a), n(b)), U.is_le_to_nat(a, b)), h)

def nle(+a: U32, +b: U32, +h: {Nat.is_le(n(a), n(b)) == True{} : Bool}) -> {U32.is_le(a, b) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(a, b), Nat.is_le(n(a), n(b)), True{}, U.is_le_to_nat(a, b), h)

def une(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(n(a), n(b)) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(n(a), n(b)), U32.is_eq(a, b), False{}, Equal.sym(Bool, U32.is_eq(a, b), Nat.is_eq(n(a), n(b)), U.is_eq_to_nat(a, b)), h)

def succ_lt(+a: Nat, +b: Nat, +h: {Nat.is_le(Nat.add(a, 1n), b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  %N.le_succ_lt(a, b) : {_ == True{} : Bool}
  %N.add_one(a) : {Nat.is_le(_, b) == True{} : Bool}
  h

def le_ne_lt(+a: Nat, +b: Nat, +le: {Nat.is_le(a, b) == True{} : Bool}, +ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  %N.le_succ_lt(a, b) : {_ == True{} : Bool}
  N.le_ne(a, b, le, ne)

def or_false_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, N.true_ne_false(h))
    case False{}:
      h

def le_antisym(+a: Nat, +b: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, N.false_ne_true(h2))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, N.false_ne_true(h1))
    case 1n+p 1n+q:
      %le_antisym(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

# ---------------------------------------------------------------------------
# Field ends
# ---------------------------------------------------------------------------

def tj_view(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +ha: {U32.is_le(a, len) == True{} : Bool}) ->
  {n(M.TJ(len, t, a)) == D.first2(X(len, t), n(a), n(len), 9, 10) : Nat}:
  M.f2_view(len, t, d, a, len, 9, 10, hok, ha, N.le_refl(n(len)), {==}, {==})

def lj_view(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +ha: {U32.is_le(a, len) == True{} : Bool}) ->
  {n(M.LJ(len, t, a)) == D.first(X(len, t), n(a), n(len), 10) : Nat}:
  M.f1_view(len, t, d, a, len, 10, hok, ha, N.le_refl(n(len)), {==})

# The end e of a field from a: the first tab or LF, inside the buffer.
def FF(+len: U32, +t: AT.Tree<U32>, +a: Nat, +e: U32) -> Type:
  {D.first2(X(len, t), a, n(len), 9, 10) == n(e) : Nat} & ({Nat.is_le(a, n(e)) == True{} : Bool} & {Nat.is_lt(n(e), n(len)) == True{} : Bool})

def ff_k(+len: U32, +t: AT.Tree<U32>, +a: Nat, +e: U32, +f: Nat,
  +hv: {n(e) == f : Nat},
  +hr: {(Nat.is_le(a, f) && Nat.is_le(f, n(len))) == True{} : Bool},
  +hne: {U32.is_eq(e, len) == False{} : Bool}) ->
  {f == n(e) : Nat} & ({Nat.is_le(a, n(e)) == True{} : Bool} & {Nat.is_lt(n(e), n(len)) == True{} : Bool}):
  +fe = Equal.sym(Nat, n(e), f, hv)
  +le1 = AB.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, f, n(e), fe, N.and_true_l(Nat.is_le(a, f), Nat.is_le(f, n(len)), hr))
  +le2 = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, f, n(e), fe, N.and_true_r(Nat.is_le(a, f), Nat.is_le(f, n(len)), hr))
  (fe, (le1, le_ne_lt(n(e), n(len), le2, une(e, len, hne))))

def fld_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +ha: {U32.is_le(a, len) == True{} : Bool},
  +hp: {M.TP(len, t, a) == False{} : Bool}) -> FF(len, t, n(a), M.TJ(len, t, a)):
  +xs = X(len, t)
  +hft = ule(a, len, ha)
  +ht = le_len(len, t, d, n(len), hok, N.le_refl(n(len)))
  ff_k(len, t, n(a), M.TJ(len, t, a), D.first2(xs, n(a), n(len), 9, 10), tj_view(len, t, d, a, hok, ha),
    PL.first2_range(xs, n(a), n(len), 9, 10, hft, ht), hp)

def tabget(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +c: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hq: {U32.is_eq(C.AT(len, t, j), c) == True{} : Bool}) -> {List.get(&2, U32, X(len, t), n(j)) == Some{c} : Maybe<&2, U32>}:
  AB.subst(U32, z => {List.get(&2, U32, X(len, t), n(j)) == Some{z} : Maybe<&2, U32>}, C.AT(len, t, j), c,
    U.is_eq_true(C.AT(len, t, j), c, hq), PF.step_get(len, t, d, j, hok, hlt))

# One past an end inside the buffer.
def nxt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool}) ->
  {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat} & {U32.is_le((j + 1 : U32), len) == True{} : Bool}:
  +h4 = N.lt_le_trans(n(j), n(len), Nat.mul(4n, Nat.pow(2n, d)), hlt, C.ok_len(len, t, d, hok))
  +inc = C.inc_fits(j, d, C.ok_d(len, t, d, hok), h4)
  (inc, nle((j + 1 : U32), len, AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, Nat.add(n(j), 1n), n((j + 1 : U32)),
    Equal.sym(Nat, n((j + 1 : U32)), Nat.add(n(j), 1n), inc), C.succ_le(n(j), n(len), hlt))))

def ne_tf(+b: Bool, +h1: {b == True{} : Bool}, +h2: {b == False{} : Bool}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, h1), h2))

def or_false_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.true_ne_false(h))
    case False{}:
      {==}

def has_get(+xs: List<&2, U32>, +e: Nat, +c: U32, +c2: U32, +hg: {List.get(&2, U32, xs, e) == Some{c} : Maybe<&2, U32>}) ->
  {D.has(xs, e, c2) == U32.is_eq(c, c2) : Bool}:
  AB.subst(Maybe<&2, U32>, m => {D.is_some(m, c2) == U32.is_eq(c, c2) : Bool}, Some{c}, List.get(&2, U32, xs, e), Equal.sym(Maybe<&2, U32>, List.get(&2, U32, xs, e), Some{c}, hg), {==})

# ---------------------------------------------------------------------------
# The first c in a .. L-1 is g when g holds c (if below L) and nothing
# before it does
# ---------------------------------------------------------------------------

def unq.k(+xs: List<&2, U32>, +a: Nat, +g: Nat, +L: Nat, +c: U32, +f: Nat, +hf: {D.first(xs, a, L, c) == f : Nat},
  +b1: Bool, +hb1: {Nat.is_lt(f, g) == b1 : Bool}, +b2: Bool, +hb2: {Nat.is_lt(g, f) == b2 : Bool},
  +hag: {Nat.is_le(a, g) == True{} : Bool}, +hgL: {Nat.is_le(g, L) == True{} : Bool}, +hL: {Nat.is_le(L, List.length(&2, U32, xs)) == True{} : Bool},
  +haL: {Nat.is_le(a, L) == True{} : Bool}, +haf: {Nat.is_le(a, f) == True{} : Bool}, +hfL: {Nat.is_le(f, L) == True{} : Bool},
  hhit: {Nat.is_lt(g, L) == True{} : Bool} -> {D.has(xs, g, c) == True{} : Bool},
  hmiss: @k: Nat -> {Nat.is_le(a, k) == True{} : Bool} -> {Nat.is_lt(k, g) == True{} : Bool} -> {D.has(xs, k, c) == False{} : Bool}) ->
  {f == g : Nat}:
  match b1 b2:
    case True{} _:
      +hit = PL.first_hit(xs, a, L, c, haL, hL, AB.subst(Nat, z => {Nat.is_lt(z, L) == True{} : Bool}, f, D.first(xs, a, L, c), Equal.sym(Nat, D.first(xs, a, L, c), f, hf), N.lt_le_trans(f, g, L, hb1, hgL)))
      +hit2 = AB.subst(Nat, z => {D.has(xs, z, c) == True{} : Bool}, D.first(xs, a, L, c), f, hf, hit)
      Empty.absurd({f == g : Nat}, ne_tf(D.has(xs, f, c), hit2, hmiss(f, haf, hb1)))
    case False{} True{}:
      +miss = PL.first_miss(xs, a, L, c, g, hag, AB.subst(Nat, z => {Nat.is_lt(g, z) == True{} : Bool}, f, D.first(xs, a, L, c), Equal.sym(Nat, D.first(xs, a, L, c), f, hf), hb2))
      Empty.absurd({f == g : Nat}, ne_tf(D.has(xs, g, c), hhit(N.lt_le_trans(g, f, L, hb2, hfL)), miss))
    case False{} False{}:
      le_antisym(f, g, N.not_lt_le(g, f, hb2), N.not_lt_le(f, g, hb1))

def unq(+xs: List<&2, U32>, +a: Nat, +g: Nat, +L: Nat, +c: U32,
  +hag: {Nat.is_le(a, g) == True{} : Bool}, +hgL: {Nat.is_le(g, L) == True{} : Bool}, +hL: {Nat.is_le(L, List.length(&2, U32, xs)) == True{} : Bool},
  hhit: {Nat.is_lt(g, L) == True{} : Bool} -> {D.has(xs, g, c) == True{} : Bool},
  hmiss: @k: Nat -> {Nat.is_le(a, k) == True{} : Bool} -> {Nat.is_lt(k, g) == True{} : Bool} -> {D.has(xs, k, c) == False{} : Bool}) ->
  {D.first(xs, a, L, c) == g : Nat}:
  +f = D.first(xs, a, L, c)
  +haL = N.le_trans(a, g, L, hag, hgL)
  +hr = PL.first_range(xs, a, L, c, haL, hL)
  unq.k(xs, a, g, L, c, f, {==}, Nat.is_lt(f, g), {==}, Nat.is_lt(g, f), {==}, hag, hgL, hL, haL,
    N.and_true_l(Nat.is_le(a, f), Nat.is_le(f, L), hr), N.and_true_r(Nat.is_le(a, f), Nat.is_le(f, L), hr), hhit, hmiss)

def lt_f2(+xs: List<&2, U32>, +a: Nat, +L: Nat, +e: Nat, +k: Nat, +hff: {D.first2(xs, a, L, 9, 10) == e : Nat},
  +h: {Nat.is_lt(k, e) == True{} : Bool}) -> {Nat.is_lt(k, D.first2(xs, a, L, 9, 10)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, e, D.first2(xs, a, L, 9, 10), Equal.sym(Nat, D.first2(xs, a, L, 9, 10), e, hff), h)

# Before the first tab or LF there is no LF, nor a tab.
def no10(+xs: List<&2, U32>, +a: Nat, +L: Nat, +e: Nat, +k: Nat, +hff: {D.first2(xs, a, L, 9, 10) == e : Nat},
  +hk1: {Nat.is_le(a, k) == True{} : Bool}, +hk2: {Nat.is_lt(k, e) == True{} : Bool}) -> {D.has(xs, k, 10) == False{} : Bool}:
  or_false_r(D.is_some(List.get(&2, U32, xs, k), 9), D.is_some(List.get(&2, U32, xs, k), 10),
    PL.first2_miss(xs, a, L, 9, 10, k, hk1, lt_f2(xs, a, L, e, k, hff, hk2)))

def no9(+xs: List<&2, U32>, +a: Nat, +L: Nat, +e: Nat, +k: Nat, +hff: {D.first2(xs, a, L, 9, 10) == e : Nat},
  +hk1: {Nat.is_le(a, k) == True{} : Bool}, +hk2: {Nat.is_lt(k, e) == True{} : Bool}) -> {D.has(xs, k, 9) == False{} : Bool}:
  or_false_l(D.is_some(List.get(&2, U32, xs, k), 9), D.is_some(List.get(&2, U32, xs, k), 10),
    PL.first2_miss(xs, a, L, 9, 10, k, hk1, lt_f2(xs, a, L, e, k, hff, hk2)))

def miss3.k(+xs: List<&2, U32>, +a: Nat, +e: Nat, +L: Nat, +k: Nat, +hff: {D.first2(xs, a, L, 9, 10) == e : Nat},
  +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>}, +g: Nat, +hg: {D.first(xs, Nat.add(e, 1n), L, 10) == g : Nat},
  +b1: Bool, +hb1: {Nat.is_lt(k, e) == b1 : Bool}, +b2: Bool, +hb2: {Nat.is_eq(e, k) == b2 : Bool},
  +hk1: {Nat.is_le(a, k) == True{} : Bool}, +hk2: {Nat.is_lt(k, g) == True{} : Bool}) -> {D.has(xs, k, 10) == False{} : Bool}:
  match b1 b2:
    case True{} _:
      no10(xs, a, L, e, k, hff, hk1, hb1)
    case False{} True{}:
      AB.subst(Nat, z => {D.has(xs, z, 10) == False{} : Bool}, e, k, N.eq_sound(e, k, hb2), has_get(xs, e, 9, 10, htab))
    case False{} False{}:
      +hek = C.succ_le(e, k, le_ne_lt(e, k, N.not_lt_le(k, e, hb1), hb2))
      PL.first_miss(xs, Nat.add(e, 1n), L, 10, k, hek, AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, g, D.first(xs, Nat.add(e, 1n), L, 10), Equal.sym(Nat, D.first(xs, Nat.add(e, 1n), L, 10), g, hg), hk2))

# The first LF from a, past a tab at e that ends a field from a.
def skip10(+xs: List<&2, U32>, +a: Nat, +e: Nat, +L: Nat, +hL: {Nat.is_le(L, List.length(&2, U32, xs)) == True{} : Bool},
  +hff: {D.first2(xs, a, L, 9, 10) == e : Nat}, +hae: {Nat.is_le(a, e) == True{} : Bool}, +hel: {Nat.is_lt(e, L) == True{} : Bool},
  +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>}) ->
  {D.first(xs, a, L, 10) == D.first(xs, Nat.add(e, 1n), L, 10) : Nat}:
  +e1 = Nat.add(e, 1n)
  +g = D.first(xs, e1, L, 10)
  +heL = C.succ_le(e, L, hel)
  +hr = PL.first_range(xs, e1, L, 10, heL, hL)
  +h1 = N.and_true_l(Nat.is_le(e1, g), Nat.is_le(g, L), hr)
  +h2 = N.and_true_r(Nat.is_le(e1, g), Nat.is_le(g, L), hr)
  +hag = N.le_trans(a, e, g, hae, N.le_trans(e, e1, g, N.le_add_r(e, 1n), h1))
  unq(xs, a, g, L, 10, hag, h2, hL, h => PL.first_hit(xs, e1, L, 10, heL, hL, h),
    +k => hk1 => hk2 => miss3.k(xs, a, e, L, k, hff, htab, g, {==}, Nat.is_lt(k, e), {==}, Nat.is_eq(e, k), {==}, hk1, hk2))

# The first LF from a is the LF that ends a field from a.
def hit10(+xs: List<&2, U32>, +a: Nat, +e: Nat, +L: Nat, +hL: {Nat.is_le(L, List.length(&2, U32, xs)) == True{} : Bool},
  +hff: {D.first2(xs, a, L, 9, 10) == e : Nat}, +hae: {Nat.is_le(a, e) == True{} : Bool}, +hel: {Nat.is_lt(e, L) == True{} : Bool},
  +hlf: {List.get(&2, U32, xs, e) == Some{10} : Maybe<&2, U32>}) ->
  {D.first(xs, a, L, 10) == e : Nat}:
  unq(xs, a, e, L, 10, hae, N.lt_to_le(e, L, hel), hL, h => has_get(xs, e, 10, 10, hlf),
    +k => hk1 => hk2 => no10(xs, a, L, e, k, hff, hk1, hk2))

# The first tab from a, before B, is the tab that ends a field from a.
def first9(+xs: List<&2, U32>, +a: Nat, +e: Nat, +B: Nat, +L: Nat, +hB: {Nat.is_le(B, List.length(&2, U32, xs)) == True{} : Bool},
  +hff: {D.first2(xs, a, L, 9, 10) == e : Nat}, +hae: {Nat.is_le(a, e) == True{} : Bool}, +heB: {Nat.is_lt(e, B) == True{} : Bool},
  +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>}) ->
  {D.first(xs, a, B, 9) == e : Nat}:
  unq(xs, a, e, B, 9, hae, N.lt_to_le(e, B, heB), hB, h => has_get(xs, e, 9, 9, htab),
    +k => hk1 => hk2 => no9(xs, a, L, e, k, hff, hk1, hk2))

# Projections of the facts.
def ff1(+len: U32, +t: AT.Tree<U32>, +a: Nat, +e: U32, r: FF(len, t, a, e)) -> {D.first2(X(len, t), a, n(len), 9, 10) == n(e) : Nat}:
  match r:
    case (x, y):
      x

def ff2(+len: U32, +t: AT.Tree<U32>, +a: Nat, +e: U32, r: FF(len, t, a, e)) -> {Nat.is_le(a, n(e)) == True{} : Bool}:
  match r:
    case (x, y):
      match y:
        case (u, v):
          u

def ff3(+len: U32, +t: AT.Tree<U32>, +a: Nat, +e: U32, r: FF(len, t, a, e)) -> {Nat.is_lt(n(e), n(len)) == True{} : Bool}:
  match r:
    case (x, y):
      match y:
        case (u, v):
          v

def NXT(+len: U32, +j: U32) -> Type:
  {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat} & {U32.is_le((j + 1 : U32), len) == True{} : Bool}

def nx1(+len: U32, +j: U32, r: NXT(len, j)) -> {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat}:
  match r:
    case (x, y):
      x

def nx2(+len: U32, +j: U32, r: NXT(len, j)) -> {U32.is_le((j + 1 : U32), len) == True{} : Bool}:
  match r:
    case (x, y):
      y

def some_of(+m: Maybe<&2, U32>, +c: U32, +h: {D.is_some(m, c) == True{} : Bool}) -> {m == Some{c} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{c} : Maybe<&2, U32>}, N.false_ne_true(h))
    case Some{+x}:
      Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, x, c, U.is_eq_true(x, c, h))

def or_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, +ha: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, N.true_ne_false(ha))
    case False{}:
      h

# INFO ends at the LF.
def lf10(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hfe: {D.first2(X(len, t), a, n(len), 9, 10) == n(e) : Nat}, +hae: {Nat.is_le(a, n(e)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(e), n(len)) == True{} : Bool}, +hq: {U32.is_eq(C.AT(len, t, e), 9) == False{} : Bool}) ->
  {List.get(&2, U32, X(len, t), n(e)) == Some{10} : Maybe<&2, U32>}:
  +xs = X(len, t)
  +f = D.first2(xs, a, n(len), 9, 10)
  +hal = N.le_trans(a, n(e), n(len), hae, N.lt_to_le(n(e), n(len), hlt))
  +hit = PL.first2_hit(xs, a, n(len), 9, 10, hal, le_len(len, t, d, n(len), hok, N.le_refl(n(len))),
    AB.subst(Nat, z => {Nat.is_lt(z, n(len)) == True{} : Bool}, n(e), f, Equal.sym(Nat, f, n(e), hfe), hlt))
  +hit2 = AB.subst(Nat, z => {D.has2(xs, z, 9, 10) == True{} : Bool}, f, n(e), hfe, hit)
  +x = C.AT(len, t, e)
  +g = PF.step_get(len, t, d, e, hok, hlt)
  +hit3 = AB.subst(Maybe<&2, U32>, m => {(D.is_some(m, 9) || D.is_some(m, 10)) == True{} : Bool}, List.get(&2, U32, xs, n(e)), Some{x}, g, hit2)
  AB.subst(U32, z => {List.get(&2, U32, xs, n(e)) == Some{z} : Maybe<&2, U32>}, x, 10,
    U.is_eq_true(x, 10, or_r(U32.is_eq(x, 9), U32.is_eq(x, 10), hit3, hq)), g)

# The first LF after a tab ending INFO.
def LFF(+len: U32, +t: AT.Tree<U32>, +a: Nat, +j: U32) -> Type:
  {n(j) == D.first(X(len, t), a, n(len), 10) : Nat} & ({Nat.is_le(a, n(j)) == True{} : Bool} & ({Nat.is_lt(n(j), n(len)) == True{} : Bool} & {List.get(&2, U32, X(len, t), n(j)) == Some{10} : Maybe<&2, U32>}))

def lff(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +ha: {U32.is_le(a, len) == True{} : Bool}, +hp: {U32.is_eq(M.LJ(len, t, a), len) == False{} : Bool}) -> LFF(len, t, n(a), M.LJ(len, t, a)):
  +xs = X(len, t)
  +j = M.LJ(len, t, a)
  +f = D.first(xs, n(a), n(len), 10)
  +hv = lj_view(len, t, d, a, hok, ha)
  +hL = le_len(len, t, d, n(len), hok, N.le_refl(n(len)))
  +hr = PL.first_range(xs, n(a), n(len), 10, ule(a, len, ha), hL)
  +fe = Equal.sym(Nat, n(j), f, hv)
  +le1 = AB.subst(Nat, z => {Nat.is_le(n(a), z) == True{} : Bool}, f, n(j), fe, N.and_true_l(Nat.is_le(n(a), f), Nat.is_le(f, n(len)), hr))
  +le2 = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, f, n(j), fe, N.and_true_r(Nat.is_le(n(a), f), Nat.is_le(f, n(len)), hr))
  +lt = le_ne_lt(n(j), n(len), le2, une(j, len, hp))
  +hit = PL.first_hit(xs, n(a), n(len), 10, ule(a, len, ha), hL, AB.subst(Nat, z => {Nat.is_lt(z, n(len)) == True{} : Bool}, n(j), f, hv, lt))
  +hit2 = AB.subst(Nat, z => {D.has(xs, z, 10) == True{} : Bool}, f, n(j), fe, hit)
  (hv, (le1, (lt, some_of(List.get(&2, U32, xs, n(j)), 10, hit2))))

def lff1(+len: U32, +t: AT.Tree<U32>, +a: Nat, +j: U32, r: LFF(len, t, a, j)) -> {n(j) == D.first(X(len, t), a, n(len), 10) : Nat}:
  match r:
    case (x, y):
      x

def lff2(+len: U32, +t: AT.Tree<U32>, +a: Nat, +j: U32, r: LFF(len, t, a, j)) -> {Nat.is_le(a, n(j)) == True{} : Bool}:
  match r:
    case (x, y):
      match y:
        case (u, v):
          u

def lff3(+len: U32, +t: AT.Tree<U32>, +a: Nat, +j: U32, r: LFF(len, t, a, j)) -> {Nat.is_lt(n(j), n(len)) == True{} : Bool}:
  match r:
    case (x, y):
      match y:
        case (u, v):
          match v:
            case (p, q):
              p

def lff4(+len: U32, +t: AT.Tree<U32>, +a: Nat, +j: U32, r: LFF(len, t, a, j)) -> {List.get(&2, U32, X(len, t), n(j)) == Some{10} : Maybe<&2, U32>}:
  match r:
    case (x, y):
      match y:
        case (u, v):
          match v:
            case (p, q):
              q
