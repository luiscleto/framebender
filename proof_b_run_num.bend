import Base
import ./norm_run.bend as NR
import ./proof_b_run_lem.bend as LM
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_index.bend as I
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Numbers for the run area: U32 shifts as powers of two, NR.depth's bounds,
# and the sizes the machine works with. Big bounds stay symbolic
# (Nat.pow(2n, e)); only small Nats are ever evaluated.

# 2^31 is always written Nat.mul(4n, Nat.pow(2n, 29n)), as D.ok writes the
# size of a block of depth 29: a name for it would make the checker unfold it.

# Powers of two
# =============

law mul4:
  for +x: Nat
  {Nat.mul(2n, Nat.mul(2n, x)) == Nat.mul(4n, x) : Nat}

def mul4(x):
  Equal.sym(Nat, Nat.mul(Nat.mul(2n, 2n), x), Nat.mul(2n, Nat.mul(2n, x)), N.mul_assoc(2n, 2n, x))

law lt_dbl:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.double(a), Nat.double(b)) == True{} : Bool}

def lt_dbl(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(Nat.double(1n+p), 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+p 1n+q:
      lt_dbl(p, q, h)

# x < 4 * 2^d gives 2x < 2^e for e = 3 + d (e stays a variable: callers
# pass e = 32n, so 2^32 is never unfolded).
law dbl_lt:
  for +d: Nat
  for +e: Nat
  for +he: {Nat.add(3n, d) == e : Nat}
  for +m: Nat
  for +hm: {2n == m : Nat}
  for +x: Nat
  for +h: {Nat.is_lt(x, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {Nat.is_lt(Nat.mul(x, m), Nat.pow(2n, e)) == True{} : Bool}

def dbl_lt(d, e, he, m, hm, x, h):
  +P = Nat.pow(2n, d)
  %hm : {Nat.is_lt(Nat.mul(x, _), Nat.pow(2n, e)) == True{} : Bool}
  %he : {Nat.is_lt(Nat.mul(x, 2n), Nat.pow(2n, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(2n, Nat.mul(2n, P)), Nat.mul(4n, P), mul4(P)) : {Nat.is_lt(Nat.mul(x, 2n), Nat.mul(2n, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(x, 2n), Nat.double(x), N.mul2_r(x)) : {Nat.is_lt(_, Nat.mul(2n, Nat.mul(4n, P))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(2n, Nat.mul(4n, P)), Nat.double(Nat.mul(4n, P)), N.mul2(Nat.mul(4n, P))) : {Nat.is_lt(Nat.double(x), _) == True{} : Bool}
  lt_dbl(x, Nat.mul(4n, P), h)

law le_dbl:
  for +x: Nat
  {Nat.is_le(x, Nat.mul(x, 2n)) == True{} : Bool}

def le_dbl(x):
  %Equal.sym(Nat, Nat.mul(x, 2n), Nat.double(x), N.mul2_r(x)) : {Nat.is_le(x, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.double(x), Nat.add(x, x), N.dbl_add(x)) : {Nat.is_le(x, _) == True{} : Bool}
  N.le_add_r(x, x)

# A * 2 does not wrap below 2^31.
law mul2_fits:
  for +a: U32
  for +h: {Nat.is_lt(U32.to_nat(a), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {U32.to_nat((a * 2 : U32)) == Nat.mul(U32.to_nat(a), 2n) : Nat}

def mul2_fits(a, h):
  U.to_nat_mul_fits_p(a, 2, dbl_lt(29n, 32n, {==}, U32.to_nat(2), {==}, U32.to_nat(a), h))

# 2^(e+1) = 2^e + 2^e.
law pow_dbl:
  for +e: Nat
  {Nat.pow(2n, 1n+e) == Nat.add(Nat.pow(2n, e), Nat.pow(2n, e)) : Nat}

def pow_dbl(e):
  +X = Nat.pow(2n, e)
  %Equal.sym(Nat, Nat.add(X, 0n), X, N.add_zero(X)) : {Nat.add(X, _) == Nat.add(X, X) : Nat}
  {==}

law shln_add:
  for +a: U32
  for +m: Nat
  for +d: Nat
  {U32.shln(U32.shln(a, m), d) == U32.shln(a, Nat.add(d, m)) : U32}

def shln_add(a, m, d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      %shln_add(a, m, p) : {U32.shl(U32.shln(U32.shln(a, m), p)) == U32.shl(_) : U32}
      {==}

# 4 << d is 4 * 2^d (d <= 29).
law sh4:
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  {U32.to_nat(U32.shln(4, d)) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}

def sh4(d, hd):
  +e1 = shln_add(1, 2n, d)
  +hlt = AB.subst(Nat, y => {Nat.is_lt(y, 32n) == True{} : Bool}, Nat.add(2n, d), Nat.add(d, 2n), N.add_comm(2n, d), C.he32(d, hd))
  +e2 = I.size_n(Nat.add(d, 2n), hlt)
  %Equal.sym(U32, U32.shln(4, d), U32.shln(1, Nat.add(d, 2n)), e1) : {U32.to_nat(_) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.shln(1, Nat.add(d, 2n))), Nat.pow(2n, Nat.add(d, 2n)), e2) : {_ == Nat.mul(4n, Nat.pow(2n, d)) : Nat}
  %N.add_comm(2n, d) : {Nat.pow(2n, _) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}
  mul4(Nat.pow(2n, d))

# Conversions done with the bound M a variable (with M a closed big number,
# any conversion in the same type makes the checker unfold it).
law le_c8:
  for +x: Nat
  for +M: Nat
  for +h: {Nat.is_le(Nat.add(x, 8n), M) == True{} : Bool}
  {Nat.is_le(Nat.add(x, U32.to_nat(8)), M) == True{} : Bool}

def le_c8(x, M, h):
  h

# NR.depth
# ========

law fd_le:
  for +f: Nat
  for +d: Nat
  for +h: {Nat.add(f, d) == 29n : Nat}
  {Nat.is_le(d, 29n) == True{} : Bool}

def fd_le(f, d, h):
  AB.subst(Nat, y => {Nat.is_le(d, y) == True{} : Bool}, Nat.add(f, d), 29n, h, N.le_add_l(d, f))

law fd_step:
  for +g: Nat
  for +d: Nat
  for +h: {Nat.add(1n+g, d) == 29n : Nat}
  {Nat.add(g, Nat.add(d, 1n)) == 29n : Nat}

def fd_step(g, d, h):
  %Equal.sym(Nat, Nat.add(d, 1n), 1n+d, N.add_one(d)) : {Nat.add(g, _) == 29n : Nat}
  %Equal.sym(Nat, Nat.add(g, 1n+d), 1n+Nat.add(g, d), N.add_succ(g, d)) : {_ == 29n : Nat}
  h

# Any x below need and below 2^31 fits the block depth.go picks.
law dbound:
  for +f: Nat
  for +d: Nat
  for +need: U32
  for +x: Nat
  for +c: Bool
  for +hc: {U32.is_le(need, U32.shln(4, d)) == c : Bool}
  for +hfd: {Nat.add(f, d) == 29n : Nat}
  for +hx1: {Nat.is_le(x, U32.to_nat(need)) == True{} : Bool}
  for +hx2: {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, NR.depth.go(f, d, need)))) == True{} : Bool}

def dbound(f, d, need, x, c, hc, hfd, hx1, hx2):
  match f c:
    case 0n _:
      AB.subst(Nat, y => {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, y))) == True{} : Bool}, 29n, d, Equal.sym(Nat, d, 29n, hfd), hx2)
    case 1n+g True{}:
      %Equal.sym(Bool, U32.is_le(need, U32.shln(4, d)), True{}, hc) :
        {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, Bool.pick(Nat, _, d, NR.depth.go(g, Nat.add(d, 1n), need))))) == True{} : Bool}
      +hd = fd_le(1n+g, d, hfd)
      +h1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(need), U32.to_nat(U32.shln(4, d))), U32.is_le(need, U32.shln(4, d)), True{},
        Equal.sym(Bool, U32.is_le(need, U32.shln(4, d)), Nat.is_le(U32.to_nat(need), U32.to_nat(U32.shln(4, d))), U.is_le_to_nat(need, U32.shln(4, d))), hc)
      +h2 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(need), y) == True{} : Bool}, U32.to_nat(U32.shln(4, d)), Nat.mul(4n, Nat.pow(2n, d)), sh4(d, hd), h1)
      N.le_trans(x, U32.to_nat(need), Nat.mul(4n, Nat.pow(2n, d)), hx1, h2)
    case 1n+g False{}:
      %Equal.sym(Bool, U32.is_le(need, U32.shln(4, d)), False{}, hc) :
        {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, Bool.pick(Nat, _, d, NR.depth.go(g, Nat.add(d, 1n), need))))) == True{} : Bool}
      dbound(g, Nat.add(d, 1n), need, x, U32.is_le(need, U32.shln(4, Nat.add(d, 1n))), {==}, fd_step(g, d, hfd), hx1, hx2)

law dle:
  for +f: Nat
  for +d: Nat
  for +need: U32
  for +c: Bool
  for +hc: {U32.is_le(need, U32.shln(4, d)) == c : Bool}
  for +hfd: {Nat.add(f, d) == 29n : Nat}
  {Nat.is_le(NR.depth.go(f, d, need), 29n) == True{} : Bool}

def dle(f, d, need, c, hc, hfd):
  match f c:
    case 0n _:
      fd_le(0n, d, hfd)
    case 1n+g True{}:
      %Equal.sym(Bool, U32.is_le(need, U32.shln(4, d)), True{}, hc) :
        {Nat.is_le(Bool.pick(Nat, _, d, NR.depth.go(g, Nat.add(d, 1n), need)), 29n) == True{} : Bool}
      fd_le(1n+g, d, hfd)
    case 1n+g False{}:
      %Equal.sym(Bool, U32.is_le(need, U32.shln(4, d)), False{}, hc) :
        {Nat.is_le(Bool.pick(Nat, _, d, NR.depth.go(g, Nat.add(d, 1n), need)), 29n) == True{} : Bool}
      dle(g, Nat.add(d, 1n), need, U32.is_le(need, U32.shln(4, Nat.add(d, 1n))), {==}, fd_step(g, d, hfd))

law depth_bound:
  for +need: U32
  for +x: Nat
  for +hx1: {Nat.is_le(x, U32.to_nat(need)) == True{} : Bool}
  for +hx2: {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, NR.depth(need)))) == True{} : Bool}

def depth_bound(need, x, hx1, hx2):
  dbound(29n, 0n, need, x, U32.is_le(need, U32.shln(4, 0n)), {==}, {==}, hx1, hx2)

law depth_le:
  for +need: U32
  {Nat.is_le(NR.depth(need), 29n) == True{} : Bool}

def depth_le(need):
  dle(29n, 0n, need, U32.is_le(need, U32.shln(4, 0n)), {==}, {==})

# 4 * 2^a < 4 * 2^b gives a <= b.
law pinv.c:
  for +a: Nat
  for +b: Nat
  for +c: Bool
  for +hc: {Nat.is_le(a, b) == c : Bool}
  for +h: {Nat.is_lt(Nat.mul(4n, Nat.pow(2n, a)), Nat.mul(4n, Nat.pow(2n, b))) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def pinv.c(a, b, c, hc, h):
  match c:
    case True{}:
      hc
    case False{}:
      +hba = N.lt_to_le(b, a, N.not_le_lt(a, b, hc))
      +h4 = N.le_mul_l(4n, Nat.pow(2n, b), Nat.pow(2n, a), N.pow_le(b, a, hba))
      +hbb = N.le_lt_trans(Nat.mul(4n, Nat.pow(2n, b)), Nat.mul(4n, Nat.pow(2n, a)), Nat.mul(4n, Nat.pow(2n, b)), h4, h)
      Empty.absurd({Nat.is_le(a, b) == True{} : Bool},
        AB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.mul(4n, Nat.pow(2n, b)), Nat.mul(4n, Nat.pow(2n, b))), True{},
          Equal.sym(Bool, Nat.is_lt(Nat.mul(4n, Nat.pow(2n, b)), Nat.mul(4n, Nat.pow(2n, b))), False{}, N.lt_irrefl(Nat.mul(4n, Nat.pow(2n, b)))), hbb)))

law pinv:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(Nat.mul(4n, Nat.pow(2n, a)), Nat.mul(4n, Nat.pow(2n, b))) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def pinv(a, b, h):
  pinv.c(a, b, Nat.is_le(a, b), {==}, h)

# Sizes
# =====

# 2^e + 8 < 4 * 2^B for e = 1 + B, B >= 3 (B, e variables: callers pass
# B = 29n, e = 30n).
law b8:
  for +x: Nat
  for +B: Nat
  for +e: Nat
  for +he: {1n+B == e : Nat}
  for +hB: {Nat.is_le(3n, B) == True{} : Bool}
  for +h: {Nat.is_le(x, Nat.pow(2n, e)) == True{} : Bool}
  {Nat.is_lt(Nat.add(x, 8n), Nat.mul(4n, Nat.pow(2n, B))) == True{} : Bool}

def b8(x, B, e, he, hB, h):
  +P = Nat.pow(2n, B)
  +Q = Nat.mul(2n, P)
  +hq = AB.subst(Nat, y => {Nat.is_le(x, Nat.pow(2n, y)) == True{} : Bool}, e, 1n+B, Equal.sym(Nat, 1n+B, e, he), h)
  +h8 = N.pow_le(3n, B, hB)
  +hPQ = AB.subst(Nat, y => {Nat.is_lt(y, Nat.add(P, P)) == True{} : Bool}, Nat.add(P, 0n), P, N.add_zero(P), N.lt_add_l(P, 0n, P, N.pow_pos(B)))
  +hPQ2 = AB.subst(Nat, y => {Nat.is_lt(P, Nat.add(P, y)) == True{} : Bool}, P, Nat.add(P, 0n), Equal.sym(Nat, Nat.add(P, 0n), P, N.add_zero(P)), hPQ)
  +h8Q = N.le_lt_trans(8n, P, Q, h8, hPQ2)
  +h1 = N.le_add_mono_r(8n, x, Q, hq)
  +h2 = N.lt_add_l(Q, 8n, Q, h8Q)
  +h3 = N.le_lt_trans(Nat.add(x, 8n), Nat.add(Q, 8n), Nat.add(Q, Q), h1, h2)
  %mul4(P) : {Nat.is_lt(Nat.add(x, 8n), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Q, 0n), Q, N.add_zero(Q)) : {Nat.is_lt(Nat.add(x, 8n), Nat.add(Q, _)) == True{} : Bool}
  h3

# The same with the bound a variable, for a sum starting with to_nat(0).
law lt_c0:
  for +x: Nat
  for +M: Nat
  for +h: {Nat.is_lt(Nat.add(x, 8n), M) == True{} : Bool}
  {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(0), x), 8n), M) == True{} : Bool}

def lt_c0(x, M, h):
  h

# 4x < 4y for x < y.
law lt4:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.is_lt(Nat.mul(4n, x), Nat.mul(4n, y)) == True{} : Bool}

def lt4(x, y, h):
  %mul4(x) : {Nat.is_lt(_, Nat.mul(4n, y)) == True{} : Bool}
  %mul4(y) : {Nat.is_lt(Nat.mul(2n, Nat.mul(2n, x)), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(2n, Nat.mul(2n, x)), Nat.double(Nat.mul(2n, x)), N.mul2(Nat.mul(2n, x))) : {Nat.is_lt(_, Nat.mul(2n, Nat.mul(2n, y))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(2n, Nat.mul(2n, y)), Nat.double(Nat.mul(2n, y)), N.mul2(Nat.mul(2n, y))) : {Nat.is_lt(Nat.double(Nat.mul(2n, x)), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(2n, x), Nat.double(x), N.mul2(x)) : {Nat.is_lt(Nat.double(_), Nat.double(Nat.mul(2n, y))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(2n, y), Nat.double(y), N.mul2(y)) : {Nat.is_lt(Nat.double(Nat.double(x)), Nat.double(_)) == True{} : Bool}
  lt_dbl(Nat.double(x), Nat.double(y), lt_dbl(x, y, h))

law pow_lt1:
  for +m: Nat
  {Nat.is_lt(Nat.pow(2n, m), Nat.pow(2n, 1n+m)) == True{} : Bool}

def pow_lt1(m):
  +x = Nat.pow(2n, m)
  %Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x)) : {Nat.is_lt(x, Nat.add(x, _)) == True{} : Bool}
  AB.subst(Nat, y => {Nat.is_lt(y, Nat.add(x, x)) == True{} : Bool}, Nat.add(x, 0n), x, N.add_zero(x), N.lt_add_l(x, 0n, x, N.pow_pos(m)))

# 4 * 2^a <= 4 * 2^b gives a <= b.
law pinv_le.c:
  for +a: Nat
  for +b: Nat
  for +c: Bool
  for +hc: {Nat.is_le(a, b) == c : Bool}
  for +h: {Nat.is_le(Nat.mul(4n, Nat.pow(2n, a)), Nat.mul(4n, Nat.pow(2n, b))) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def pinv_le.c(a, b, c, hc, h):
  match c:
    case True{}:
      hc
    case False{}:
      +hba = Equal.trans(Bool, Nat.is_le(1n+b, a), Nat.is_lt(b, a), True{}, N.le_succ_lt(b, a), N.not_le_lt(a, b, hc))
      +X = Nat.mul(4n, Nat.pow(2n, b))
      +Y = Nat.mul(4n, Nat.pow(2n, 1n+b))
      +h1 = N.le_mul_l(4n, Nat.pow(2n, 1n+b), Nat.pow(2n, a), N.pow_le(1n+b, a, hba))
      +h2 = N.le_trans(Y, Nat.mul(4n, Nat.pow(2n, a)), X, h1, h)
      +h3 = N.lt_le_trans(X, Y, X, lt4(Nat.pow(2n, b), Nat.pow(2n, 1n+b), pow_lt1(b)), h2)
      Empty.absurd({Nat.is_le(a, b) == True{} : Bool},
        AB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(X, X), True{}, Equal.sym(Bool, Nat.is_lt(X, X), False{}, N.lt_irrefl(X)), h3)))

law pinv_le:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(Nat.mul(4n, Nat.pow(2n, a)), Nat.mul(4n, Nat.pow(2n, b))) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def pinv_le(a, b, h):
  pinv_le.c(a, b, Nat.is_le(a, b), {==}, h)
