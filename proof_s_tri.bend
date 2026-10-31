import Base
import ./types.bend as B
import lawful-words@0.1.0.0/proof_nat.bend as N

# The places of Number=G values (B.Gt.index) are below their count
# (B.Gt.count): k(k+1)/2 is the triangle number tri(k), so genotype j/i of a
# record with n ALTs (j <= i <= n) is at tri(i) + j < tri(n+1). Every
# variable is reusable.

def tri(+k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+m):
      Nat.add(tri(m), 1n+m)

# k(k+1) = tri(k) + tri(k).
law tri2:
  for +k: Nat
  {Nat.mul(k, 1n+k) == Nat.add(tri(k), tri(k)) : Nat}

def tri2(k):
  match k:
    case 0n:
      {==}
    case 1n+m:
      +t = tri(m)
      +T2 = Nat.add(t, t)
      +M2 = Nat.add(m, m)
      +e1 = Equal.trans(Nat, Nat.mul(m, 1n+(1n+m)), Nat.add(m, Nat.mul(m, 1n+m)), Nat.add(m, T2),
        N.mul_succ_r(m, 1n+m), Equal.cong(Nat, Nat, z => Nat.add(m, z), Nat.mul(m, 1n+m), T2, tri2(m)))
      +e2 = Equal.trans(Nat, Nat.add(m, Nat.add(m, T2)), Nat.add(M2, T2), Nat.add(T2, M2),
        Equal.sym(Nat, Nat.add(M2, T2), Nat.add(m, Nat.add(m, T2)), N.add_assoc(m, m, T2)), N.add_comm(M2, T2))
      +eL = Equal.trans(Nat, Nat.mul(1n+m, 1n+(1n+m)), 1n+(1n+Nat.add(m, Nat.add(m, T2))), 1n+(1n+Nat.add(T2, M2)),
        Equal.cong(Nat, Nat, z => 1n+(1n+Nat.add(m, z)), Nat.mul(m, 1n+(1n+m)), Nat.add(m, T2), e1),
        Equal.cong(Nat, Nat, z => 1n+(1n+z), Nat.add(m, Nat.add(m, T2)), Nat.add(T2, M2), e2))
      +eR = Equal.trans(Nat, Nat.add(Nat.add(t, 1n+m), Nat.add(t, 1n+m)), Nat.add(T2, Nat.add(1n+m, 1n+m)), 1n+(1n+Nat.add(T2, M2)),
        N.add_swap(t, 1n+m, t, 1n+m),
        Equal.trans(Nat, Nat.add(T2, 1n+Nat.add(m, 1n+m)), 1n+Nat.add(T2, Nat.add(m, 1n+m)), 1n+(1n+Nat.add(T2, M2)),
          N.add_succ(T2, Nat.add(m, 1n+m)),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(T2, Nat.add(m, 1n+m)), 1n+Nat.add(T2, M2),
            Equal.trans(Nat, Nat.add(T2, Nat.add(m, 1n+m)), Nat.add(T2, 1n+M2), 1n+Nat.add(T2, M2),
              Equal.cong(Nat, Nat, z => Nat.add(T2, z), Nat.add(m, 1n+m), 1n+M2, N.add_succ(m, m)),
              N.add_succ(T2, M2)))))
      Equal.trans(Nat, Nat.mul(1n+m, 1n+(1n+m)), 1n+(1n+Nat.add(T2, M2)), Nat.add(Nat.add(t, 1n+m), Nat.add(t, 1n+m)), eL, Equal.sym(Nat, Nat.add(Nat.add(t, 1n+m), Nat.add(t, 1n+m)), 1n+(1n+Nat.add(T2, M2)), eR))

# t + t = t * 2 + 0.
def dbl2(+t: Nat) -> {Nat.add(t, t) == Nat.add(Nat.mul(t, 2n), 0n) : Nat}:
  +e1 = Equal.trans(Nat, Nat.mul(t, 2n), Nat.add(t, Nat.mul(t, 1n)), Nat.add(t, t), N.mul_succ_r(t, 1n),
    Equal.cong(Nat, Nat, z => Nat.add(t, z), Nat.mul(t, 1n), t,
      Equal.trans(Nat, Nat.mul(t, 1n), Nat.add(t, Nat.mul(t, 0n)), t, N.mul_succ_r(t, 0n),
        Equal.trans(Nat, Nat.add(t, Nat.mul(t, 0n)), Nat.add(t, 0n), t, Equal.cong(Nat, Nat, z => Nat.add(t, z), Nat.mul(t, 0n), 0n, N.mul_zero_r(t)), N.add_zero(t)))))
  Equal.trans(Nat, Nat.add(t, t), Nat.mul(t, 2n), Nat.add(Nat.mul(t, 2n), 0n), Equal.sym(Nat, Nat.mul(t, 2n), Nat.add(t, t), e1), Equal.sym(Nat, Nat.add(Nat.mul(t, 2n), 0n), Nat.mul(t, 2n), N.add_zero(Nat.mul(t, 2n))))

# k(k+1)/2 = tri(k).
def tdiv(+k: Nat) -> {Nat.div(Nat.mul(k, 1n+k), 2n) == tri(k) : Nat}:
  Equal.trans(Nat, Nat.div(Nat.mul(k, 1n+k), 2n), Nat.div(Nat.add(Nat.mul(tri(k), 2n), 0n), 2n), tri(k),
    Equal.cong(Nat, Nat, z => Nat.div(z, 2n), Nat.mul(k, 1n+k), Nat.add(Nat.mul(tri(k), 2n), 0n), Equal.trans(Nat, Nat.mul(k, 1n+k), Nat.add(tri(k), tri(k)), Nat.add(Nat.mul(tri(k), 2n), 0n), tri2(k), dbl2(tri(k)))),
    N.div_mul_add(tri(k), 2n, 0n, {==}))

law tri_mono:
  for +i: Nat
  for +n: Nat
  for +h: {Nat.is_le(i, n) == True{} : Bool}
  {Nat.is_le(tri(i), tri(n)) == True{} : Bool}

def tri_mono(i, n, h):
  match i n:
    case 0n _:
      N.le_zero_l(tri(n))
    case 1n+(+a) 0n:
      Empty.absurd({Nat.is_le(tri(1n+a), 0n) == True{} : Bool}, N.false_ne_true(h))
    case 1n+(+a) 1n+(+b):
      N.le_trans(Nat.add(tri(a), 1n+a), Nat.add(tri(b), 1n+a), Nat.add(tri(b), 1n+b),
        N.le_add_mono_r(1n+a, tri(a), tri(b), tri_mono(a, b, h)),
        N.le_add_mono_l(tri(b), 1n+a, 1n+b, h))

def cnt_eq(+n: Nat) -> {B.Gt.count(n) == Nat.add(tri(n), 1n+n) : Nat}:
  tdiv(1n+n)

# Genotype i/i (and 0/i, and 0/0) of a record with n ALTs, i <= n: below the
# count of values.
def idx_ii(+i: Nat, +n: Nat, +h: {Nat.is_le(i, n) == True{} : Bool}) -> {Nat.is_lt(B.Gt.index(i, i), B.Gt.count(n)) == True{} : Bool}:
  +le = N.le_trans(Nat.add(tri(i), i), Nat.add(tri(n), i), Nat.add(tri(n), n), N.le_add_mono_r(i, tri(i), tri(n), tri_mono(i, n, h)), N.le_add_mono_l(tri(n), i, n, h))
  %Equal.sym(Nat, Nat.div(Nat.mul(i, 1n+i), 2n), tri(i), tdiv(i)) : {Nat.is_lt(Nat.add(_, i), B.Gt.count(n)) == True{} : Bool}
  %Equal.sym(Nat, B.Gt.count(n), Nat.add(tri(n), 1n+n), cnt_eq(n)) : {Nat.is_lt(Nat.add(tri(i), i), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(tri(n), 1n+n), 1n+Nat.add(tri(n), n), N.add_succ(tri(n), n)) : {Nat.is_lt(Nat.add(tri(i), i), _) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(Nat.add(tri(i), i), 1n+Nat.add(tri(n), n)), Nat.is_le(Nat.add(tri(i), i), Nat.add(tri(n), n)), N.lt_succ_iff(Nat.add(tri(i), i), Nat.add(tri(n), n))) : {_ == True{} : Bool}
  le

def idx_0i(+i: Nat, +n: Nat, +h: {Nat.is_le(i, n) == True{} : Bool}) -> {Nat.is_lt(B.Gt.index(0n, i), B.Gt.count(n)) == True{} : Bool}:
  N.le_lt_trans(B.Gt.index(0n, i), B.Gt.index(i, i), B.Gt.count(n),
    N.le_add_mono_l(Nat.div(Nat.mul(i, 1n+i), 2n), 0n, i, N.le_zero_l(i)), idx_ii(i, n, h))

def idx_00(+n: Nat) -> {Nat.is_lt(0n, B.Gt.count(n)) == True{} : Bool}:
  %Equal.sym(Nat, B.Gt.count(n), Nat.add(tri(n), 1n+n), cnt_eq(n)) : {Nat.is_lt(0n, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(tri(n), 1n+n), 1n+Nat.add(tri(n), n), N.add_succ(tri(n), n)) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}
