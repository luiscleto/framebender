import Base
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB

# Arithmetic of the hand-out term HO = (X - |O|) / d (proof_b_budget_need.bend,
# d = 256): writing more never raises it, and writing t >= d bytes (within X)
# lowers it by one.

def sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), N.le_add_l(p, 1n))

def sub_anti(+x: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.sub(x, b), Nat.sub(x, a)) == True{} : Bool}:
  match x a b:
    case 0n _ _:
      {==}
    case 1n+y 0n 0n:
      N.le_refl(1n+y)
    case 1n+y 0n 1n+c:
      N.le_trans(Nat.sub(y, c), y, 1n+y, sub_le(y, c), N.le_add_l(y, 1n))
    case 1n+y 1n+e 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+y, 0n), Nat.sub(1n+y, 1n+e)) == True{} : Bool}, N.false_ne_true(h))
    case 1n+y 1n+e 1n+c:
      sub_anti(y, e, c, h)

def dm.k(+x: Nat, +y: Nat, +d: Nat, b: Bool, +eb: {Nat.is_le(Nat.div(x, d), Nat.div(y, d)) == b : Bool}, +hd: {Nat.is_lt(0n, d) == True{} : Bool},
  +h: {Nat.is_le(x, y) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      +qx = Nat.div(x, d)
      +qy = Nat.div(y, d)
      +hlt = N.not_le_lt(qx, qy, eb)
      +h1 = Equal.trans(Bool, Nat.is_le(1n+qy, qx), Nat.is_lt(qy, qx), True{}, N.le_succ_lt(qy, qx), hlt)
      +ey = N.div_mod(y, d)
      +ex = N.div_mod(x, d)
      +hy = AB.subst(Nat, z => {Nat.is_lt(z, Nat.add(Nat.mul(qy, d), d)) == True{} : Bool}, Nat.add(Nat.mul(qy, d), Nat.mod(y, d)), y, ey,
        N.lt_add_l(Nat.mul(qy, d), Nat.mod(y, d), d, N.mod_lt(y, d, hd)))
      +e1 = Equal.trans(Nat, Nat.mul(1n+qy, d), Nat.mul(d, 1n+qy), Nat.add(Nat.mul(qy, d), d), N.mul_comm(1n+qy, d),
        Equal.trans(Nat, Nat.mul(d, 1n+qy), Nat.add(d, Nat.mul(d, qy)), Nat.add(Nat.mul(qy, d), d), N.mul_succ_r(d, qy),
          Equal.trans(Nat, Nat.add(d, Nat.mul(d, qy)), Nat.add(Nat.mul(d, qy), d), Nat.add(Nat.mul(qy, d), d), N.add_comm(d, Nat.mul(d, qy)),
            Equal.cong(Nat, Nat, z => Nat.add(z, d), Nat.mul(d, qy), Nat.mul(qy, d), N.mul_comm(d, qy)))))
      +h2 = N.le_trans(Nat.add(Nat.mul(qy, d), d), Nat.mul(qx, d), x,
        AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(qx, d)) == True{} : Bool}, Nat.mul(1n+qy, d), Nat.add(Nat.mul(qy, d), d), e1, N.le_mul_r(1n+qy, qx, d, h1)),
        AB.subst(Nat, z => {Nat.is_le(Nat.mul(qx, d), z) == True{} : Bool}, Nat.add(Nat.mul(qx, d), Nat.mod(x, d)), x, ex, N.le_add_r(Nat.mul(qx, d), Nat.mod(x, d))))
      +h3 = N.lt_le_trans(y, Nat.add(Nat.mul(qy, d), d), x, hy, h2)
      Empty.absurd({False{} == True{} : Bool}, N.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(y, x), False{}, Equal.sym(Bool, Nat.is_lt(y, x), True{}, h3), N.le_not_lt(x, y, h))))

# x <= y gives x / d <= y / d.
def div_mono(+x: Nat, +y: Nat, +d: Nat, +hd: {Nat.is_lt(0n, d) == True{} : Bool}, +h: {Nat.is_le(x, y) == True{} : Bool}) ->
  {Nat.is_le(Nat.div(x, d), Nat.div(y, d)) == True{} : Bool}:
  dm.k(x, y, d, Nat.is_le(Nat.div(x, d), Nat.div(y, d)), {==}, hd, h)

# Writing more never raises HO.
def ho_anti(+X: Nat, +a: Nat, +b: Nat, +d: Nat, +hd: {Nat.is_lt(0n, d) == True{} : Bool}, +h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.div(Nat.sub(X, b), d), Nat.div(Nat.sub(X, a), d)) == True{} : Bool}:
  div_mono(Nat.sub(X, b), Nat.sub(X, a), d, hd, sub_anti(X, a, b, h))

def le_zero_eq(+n: Nat, +h: {Nat.is_le(n, 0n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Empty.absurd({1n+m == 0n : Nat}, N.false_ne_true(h))

# (a + t) - ... : X - (a + t) + t = X - a when a + t <= X.
def sub_add_eq(+X: Nat, +a: Nat, +t: Nat, +h: {Nat.is_le(Nat.add(a, t), X) == True{} : Bool}) -> {Nat.add(t, Nat.sub(X, Nat.add(a, t))) == Nat.sub(X, a) : Nat}:
  match X a:
    case 0n _:
      +e = N.add_eq_zero_r(a, t, le_zero_eq(Nat.add(a, t), h))
      Equal.trans(Nat, Nat.add(t, Nat.sub(0n, Nat.add(a, t))), Nat.add(t, 0n), 0n, {==},
        Equal.trans(Nat, Nat.add(t, 0n), t, 0n, N.add_zero(t), e))
    case 1n+Y 0n:
      N.le_sub_add(t, 1n+Y, h)
    case 1n+Y 1n+b:
      sub_add_eq(Y, b, t, h)

# Writing t >= d bytes (a + t <= X) lowers HO by one.
def ho_drop(+X: Nat, +a: Nat, +t: Nat, +d: Nat, +hd: {Nat.is_lt(0n, d) == True{} : Bool}, +ht: {Nat.is_le(d, t) == True{} : Bool},
  +hp: {Nat.is_le(Nat.add(a, t), X) == True{} : Bool}) ->
  {Nat.is_le(1n+Nat.div(Nat.sub(X, Nat.add(a, t)), d), Nat.div(Nat.sub(X, a), d)) == True{} : Bool}:
  +r = Nat.sub(X, Nat.add(a, t))
  +e = sub_add_eq(X, a, t, hp)
  +h1 = N.le_add_mono_r(r, d, t, ht)
  +h2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(d, r), z) == True{} : Bool}, Nat.add(t, r), Nat.sub(X, a), Equal.trans(Nat, Nat.add(t, r), Nat.add(t, r), Nat.sub(X, a), {==}, e), h1)
  +h3 = div_mono(Nat.add(d, r), Nat.sub(X, a), d, hd, h2)
  +e2 = Equal.trans(Nat, Nat.div(Nat.add(d, r), d), Nat.div(Nat.add(Nat.mul(1n, d), r), d), Nat.add(1n, Nat.div(r, d)),
    Equal.cong(Nat, Nat, z => Nat.div(Nat.add(z, r), d), d, Nat.mul(1n, d), Equal.sym(Nat, Nat.mul(1n, d), d, N.add_zero(d))),
    N.div_add_mul(1n, d, r, hd))
  AB.subst(Nat, z => {Nat.is_le(z, Nat.div(Nat.sub(X, a), d)) == True{} : Bool}, Nat.div(Nat.add(d, r), d), 1n+Nat.div(r, d), e2, h3)
