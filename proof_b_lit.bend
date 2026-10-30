import Base
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_b_defs.bend as P
import ./norm_seq.bend as Norm

# Bridges between big literal bounds and powers of two (shared by every
# phase-B area). The checker must never compute either side: a literal
# (one number) and a power (expanded to unary) are related through a word
# shift, which the checker evaluates natively: shln(1, k) == w, then
# to_nat(w) == 2^k (lawful-words' to_nat_shln_fits). Exponents stay
# variables in every proof here; they are instantiated only at the end.

# x < x + x when x > 0.
def lt_twice(+x: Nat, h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(x, x)) == True{} : Bool}:
  %N.add_zero(x) : {Nat.is_lt(_, Nat.add(x, x)) == True{} : Bool}
  N.lt_add_l(x, 0n, x, h)

# 2^m < 2^(1+m), for a variable m.
def pow_lt1(+m: Nat) -> {Nat.is_lt(Nat.pow(2n, m), Nat.pow(2n, 1n+m)) == True{} : Bool}:
  +x = Nat.pow(2n, m)
  %Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x)) : {Nat.is_lt(x, Nat.add(x, _)) == True{} : Bool}
  lt_twice(x, N.pow_pos(m))

def lt.le(+m: Nat, +k: Nat, h: {Nat.is_lt(m, k) == True{} : Bool}) -> {Nat.is_le(1n+m, k) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(1n+m, k), Nat.is_lt(m, k), N.le_succ_lt(m, k)) : {_ == True{} : Bool}
  h

# 2^m < 2^k when m < k.
def pow_lt(+m: Nat, +k: Nat, h: {Nat.is_lt(m, k) == True{} : Bool}) -> {Nat.is_lt(Nat.pow(2n, m), Nat.pow(2n, k)) == True{} : Bool}:
  N.lt_le_trans(Nat.pow(2n, m), Nat.pow(2n, 1n+m), Nat.pow(2n, k), pow_lt1(m), N.pow_le(1n+m, k, lt.le(m, k, h)))

# The fit hypothesis of to_nat_shln_fits for a = 1, for any bound M (M stays
# abstract here: the checker would expand a power of two it has to compare).
def lit.h(+k: Nat, +M: Nat, h: {Nat.is_lt(Nat.pow(2n, k), M) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(U32.to_nat(1), Nat.pow(2n, k)), M) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.pow(2n, k), 0n), Nat.pow(2n, k), N.add_zero(Nat.pow(2n, k))) : {Nat.is_lt(_, M) == True{} : Bool}
  h

# The word shln(1, k) is 2^k (k < 32).
def shl1(+k: Nat, h: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {U32.to_nat(U32.shln(1, k)) == Nat.pow(2n, k) : Nat}:
  +x = Nat.pow(2n, k)
  +e = U.to_nat_shln_fits_p(1, k, lit.h(k, Nat.pow(2n, 32n), pow_lt(k, 32n, h)))
  %N.add_zero(x) : {U32.to_nat(U32.shln(1, k)) == _ : Nat}
  e

# A literal is the power it equals: w is the word shln(1, k).
def lit_pow(+k: Nat, +w: U32, hw: {U32.shln(1, k) == w : U32}, h: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {U32.to_nat(w) == Nat.pow(2n, k) : Nat}:
  %hw : {U32.to_nat(_) == Nat.pow(2n, k) : Nat}
  shl1(k, h)

# The bounds phase B uses, as words.
def lit28w() -> {U32.to_nat(268435456) == Nat.pow(2n, 28n) : Nat}:
  lit_pow(28n, 268435456, {==}, {==})

def lit31w() -> {U32.to_nat(2147483648) == Nat.pow(2n, 31n) : Nat}:
  lit_pow(31n, 2147483648, {==}, {==})


# A word at most 2^31 reads as at most 2^31.
def le31.b(+u: U32, hb: {U32.is_le(u, 2147483648) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(u), Nat.pow(2n, 31n)) == True{} : Bool}:
  %lit31w() : {Nat.is_le(U32.to_nat(u), _) == True{} : Bool}
  %U.is_le_to_nat(u, 2147483648) : {_ == True{} : Bool}
  hb

def le31.k(+n: Nat, e: {U32.to_nat(U32.from_nat(n)) == n : Nat}, hb: {U32.is_le(U32.from_nat(n), 2147483648) == True{} : Bool}) -> {Nat.is_le(n, Nat.pow(2n, 31n)) == True{} : Bool}:
  %e : {Nat.is_le(_, Nat.pow(2n, 31n)) == True{} : Bool}
  le31.b(U32.from_nat(n), hb)

# le31(n): n is at most 2^31.
def le31_le(+n: Nat, +h: {P.le31(n) == True{} : Bool}) -> {Nat.is_le(n, Nat.pow(2n, 31n)) == True{} : Bool}:
  le31.k(n, N.eq_sound(U32.to_nat(U32.from_nat(n)), n, N.and_true_l(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), U32.is_le(U32.from_nat(n), 2147483648), h)),
    N.and_true_r(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), U32.is_le(U32.from_nat(n), 2147483648), h))

def AB_subst_n(+a: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(a, y) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

def AB_subst_y(+a: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(a, y) == True{} : Bool}:
  AB_subst_n(a, x, y, e, h)

# From l <= m and 1 + m == x: 1 + l <= x.
def AB_subst_x(+x: Nat, +l: Nat, +m: Nat, +e: {1n+m == x : Nat}, +h: {Nat.is_le(l, m) == True{} : Bool}) -> {Nat.is_le(1n+l, x) == True{} : Bool}:
  %e : {Nat.is_le(1n+l, _) == True{} : Bool}
  h

# A word that is not zero is at least 1, and one less reads as one less.
def nz_le1(+x: Nat, +h: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_le(1n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, N.true_ne_false(h))
    case 1n+p:
      N.le_zero_l(p)

def w_le1(+w: U32, +hz: {U32.is_zero(w) == False{} : Bool}) -> {Nat.is_le(1n, U32.to_nat(w)) == True{} : Bool}:
  nz_le1(U32.to_nat(w), Equal.trans(Bool, Nat.is_eq(U32.to_nat(w), 0n), U32.is_zero(w), False{}, Equal.sym(Bool, U32.is_zero(w), Nat.is_eq(U32.to_nat(w), 0n), U.is_zero_to_nat(w)), hz))

def w_dec(+w: U32, +hz: {U32.is_zero(w) == False{} : Bool}) -> {U32.to_nat((w - 1 : U32)) == Nat.sub(U32.to_nat(w), 1n) : Nat}:
  U.to_nat_sub_le(w, 1, Equal.trans(Bool, U32.is_le(1, w), Nat.is_le(U32.to_nat(1), U32.to_nat(w)), True{}, U.is_le_to_nat(1, w), w_le1(w, hz)))

def w_zero(+w: U32, +hz: {U32.is_zero(w) == True{} : Bool}) -> {U32.to_nat(w) == 0n : Nat}:
  N.eq_sound(U32.to_nat(w), 0n, Equal.trans(Bool, Nat.is_eq(U32.to_nat(w), 0n), U32.is_zero(w), True{}, Equal.sym(Bool, U32.is_zero(w), Nat.is_eq(U32.to_nat(w), 0n), U.is_zero_to_nat(w)), hz))

def lle.go(+s: String, +z: Bool, +w: U32, +hz: {U32.is_zero(w) == z : Bool}, +h: {Norm.len_le.go(s, z, w) == True{} : Bool}) ->
  {Nat.is_le(String.length(s), U32.to_nat(w)) == True{} : Bool}:
  match s z:
    case SNil{} _:
      N.le_zero_l(U32.to_nat(w))
    case SCon{+c, +t} True{}:
      Empty.absurd({Nat.is_le(String.length(SCon{c, t}), U32.to_nat(w)) == True{} : Bool}, N.false_ne_true(h))
    case SCon{+c, +t} False{}:
      +x = U32.to_nat(w)
      +ih = lle.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32), {==}, h)
      +ih2 = AB_subst_n(String.length(t), U32.to_nat((w - 1 : U32)), Nat.sub(x, 1n), w_dec(w, hz), ih)
      AB_subst_x(x, String.length(t), Nat.sub(x, 1n), N.le_sub_add(1n, x, w_le1(w, hz)), ih2)

def lel.go(+s: String, +z: Bool, +w: U32, +hz: {U32.is_zero(w) == z : Bool}, +h: {Nat.is_le(String.length(s), U32.to_nat(w)) == True{} : Bool}) ->
  {Norm.len_le.go(s, z, w) == True{} : Bool}:
  match s z:
    case SNil{} _:
      {==}
    case SCon{+c, +t} True{}:
      +h0 = AB_subst_y(String.length(SCon{c, t}), U32.to_nat(w), 0n, w_zero(w, hz), h)
      Empty.absurd({Norm.len_le.go(SCon{c, t}, True{}, w) == True{} : Bool}, N.false_ne_true(h0))
    case SCon{+c, +t} False{}:
      +x = U32.to_nat(w)
      +h1 = N.le_sub_r(1n, String.length(t), x, h)
      lel.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32), {==},
        AB_subst_n(String.length(t), Nat.sub(x, 1n), U32.to_nat((w - 1 : U32)), Equal.sym(Nat, U32.to_nat((w - 1 : U32)), Nat.sub(x, 1n), w_dec(w, hz)), h1))

def tw_cons(+c: Char, +k: Norm.Cut2) -> {Norm.take_w.cons(c, k) == Norm.Cut2{SCon{c, Norm.Cut2.now(k)}, Norm.Cut2.later(k)} : Norm.Cut2}:
  match k:
    case Norm.Cut2{+n, +l}:
      {==}

def tw_app.go(+s: String, +z: Bool, +w: U32) ->
  {String.append(Norm.Cut2.now(Norm.take_w.go(s, z, w)), Norm.Cut2.later(Norm.take_w.go(s, z, w))) == s : String}:
  match s z:
    case SNil{} _:
      {==}
    case SCon{+c, +t} True{}:
      {==}
    case SCon{+c, +t} False{}:
      +k = Norm.take_w.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32))
      %Equal.sym(Norm.Cut2, Norm.take_w.cons(c, k), Norm.Cut2{SCon{c, Norm.Cut2.now(k)}, Norm.Cut2.later(k)}, tw_cons(c, k)) :
        {String.append(Norm.Cut2.now(_), Norm.Cut2.later(_)) == SCon{c, t} : String}
      Equal.cong(String, String, x => SCon{c, x}, String.append(Norm.Cut2.now(k), Norm.Cut2.later(k)), t, tw_app.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32)))

def tw_len.go(+s: String, +z: Bool, +w: U32, +hz: {U32.is_zero(w) == z : Bool}) ->
  {Norm.len_le(Norm.Cut2.now(Norm.take_w.go(s, z, w)), w) == True{} : Bool}:
  match s z:
    case SNil{} _:
      {==}
    case SCon{+c, +t} True{}:
      {==}
    case SCon{+c, +t} False{}:
      +k = Norm.take_w.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32))
      %Equal.sym(Norm.Cut2, Norm.take_w.cons(c, k), Norm.Cut2{SCon{c, Norm.Cut2.now(k)}, Norm.Cut2.later(k)}, tw_cons(c, k)) :
        {Norm.len_le(Norm.Cut2.now(_), w) == True{} : Bool}
      %Equal.sym(Bool, U32.is_zero(w), False{}, hz) : {Norm.len_le.go(SCon{c, Norm.Cut2.now(k)}, _, w) == True{} : Bool}
      tw_len.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32), {==})

def tw_all.go(+s: String, +z: Bool, +w: U32, +h: {Norm.len_le.go(s, z, w) == True{} : Bool}) ->
  {Norm.take_w.go(s, z, w) == Norm.Cut2{s, ""} : Norm.Cut2}:
  match s z:
    case SNil{} _:
      {==}
    case SCon{+c, +t} True{}:
      Empty.absurd({Norm.take_w.go(SCon{c, t}, True{}, w) == Norm.Cut2{SCon{c, t}, ""} : Norm.Cut2}, N.false_ne_true(h))
    case SCon{+c, +t} False{}:
      %Equal.sym(Norm.Cut2, Norm.take_w.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32)), Norm.Cut2{t, ""}, tw_all.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32), h)) :
        {Norm.take_w.cons(c, _) == Norm.Cut2{SCon{c, t}, ""} : Norm.Cut2}
      {==}

# len_le(s, w): s has at most to_nat(w) characters, and back.
def len_le_le(+s: String, +w: U32, h: {Norm.len_le(s, w) == True{} : Bool}) -> {Nat.is_le(String.length(s), U32.to_nat(w)) == True{} : Bool}:
  lle.go(s, U32.is_zero(w), w, {==}, h)

def le_len_le(+s: String, +w: U32, h: {Nat.is_le(String.length(s), U32.to_nat(w)) == True{} : Bool}) -> {Norm.len_le(s, w) == True{} : Bool}:
  lel.go(s, U32.is_zero(w), w, {==}, h)

# take_w(s, w): the first part has at most to_nat(w) characters, and the two
# parts make s; when s fits, the first part is all of it.
def take_w_ok(+s: String, +w: U32) ->
  {String.append(Norm.Cut2.now(Norm.take_w(s, w)), Norm.Cut2.later(Norm.take_w(s, w))) == s : String}
  & {Norm.len_le(Norm.Cut2.now(Norm.take_w(s, w)), w) == True{} : Bool}:
  (tw_app.go(s, U32.is_zero(w), w), tw_len.go(s, U32.is_zero(w), w, {==}))

def take_w_all(+s: String, +w: U32, h: {Norm.len_le(s, w) == True{} : Bool}) ->
  {Norm.take_w(s, w) == Norm.Cut2{s, ""} : Norm.Cut2}:
  tw_all.go(s, U32.is_zero(w), w, h)
