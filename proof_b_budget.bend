import Base
import ./protocol.bend as Pr
import ./norm_seq.bend as Norm
import ./proof_base.bend as P
import ./proof_b_cut_str.bend as S
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB

# The budget of the law machine (notes/bytes_proofs_budget.md): how many
# reads one Want asks. The count is generic (no fact about 2^31 is needed):
# parts(c, a, b) asks at most max(1, b - a) reads, and Req.of either one
# read or parts(c, a, e).

def max1(+x: Nat) -> Nat:
  Nat.max(1n, x)

def le1_max(+x: Nat) -> {Nat.is_le(1n, max1(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      N.le_zero_l(p)

def max1_eq(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {max1(x) == x : Nat}:
  match x:
    case 0n:
      Empty.absurd({max1(0n) == 0n : Nat}, N.false_ne_true(h))
    case 1n+p:
      {==}

def ne_tf(+b: Bool, +h1: {b == True{} : Bool}, +h2: {b == False{} : Bool}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, h1), h2))

# le31 holds for 0 and 1, so a window it rejects has at least 2 letters.
def ge2(+n: Nat, +h: {Norm.le31(n) == False{} : Bool}) -> {Nat.is_le(2n, n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(2n, 0n) == True{} : Bool}, N.true_ne_false(h))
    case 1n:
      Empty.absurd({Nat.is_le(2n, 1n) == True{} : Bool}, N.true_ne_false(h))
    case 2n+k:
      N.le_zero_l(k)

# 1 <= n - d gives d <= n.
def sub_pos_le(+n: Nat, +d: Nat, +h: {Nat.is_le(1n, Nat.sub(n, d)) == True{} : Bool}) -> {Nat.is_le(d, n) == True{} : Bool}:
  match n d:
    case 0n _:
      Empty.absurd({Nat.is_le(d, 0n) == True{} : Bool}, N.false_ne_true(h))
    case 1n+k 0n:
      N.le_zero_l(1n+k)
    case 1n+k 1n+e:
      sub_pos_le(k, e, h)

# Halving n >= 2 letters (n = 2q + r, r < 2): q >= 1 and n - q >= 1.
def half.k(+n: Nat, +q: Nat, +r: Nat, +dm: {Nat.add(Nat.mul(q, 2n), r) == n : Nat}, +hr: {Nat.is_lt(r, 2n) == True{} : Bool},
  +h: {Nat.is_le(2n, n) == True{} : Bool}) -> {Nat.is_le(1n, q) == True{} : Bool} & {Nat.is_le(1n, Nat.sub(n, q)) == True{} : Bool}:
  match q:
    case 0n:
      +h0 = AB.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, n, r, Equal.sym(Nat, r, n, dm), h)
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool} & {Nat.is_le(1n, Nat.sub(n, 0n)) == True{} : Bool},
        ne_tf(Nat.is_lt(r, 2n), hr, N.le_not_lt(2n, r, h0)))
    case 1n+p:
      +X = Nat.mul(p, 2n)
      +hp = N.le_trans(p, X, Nat.add(X, r), N.le_trans(p, Nat.mul(p, 1n), X,
        AB.subst(Nat, z => {Nat.is_le(p, z) == True{} : Bool}, p, Nat.mul(p, 1n), Equal.sym(Nat, Nat.mul(p, 1n), p, N.mul_one(p)), N.le_refl(p)),
        N.le_mul_l(p, 1n, 2n, {==})), N.le_add_r(X, r))
      +h1 = AB.subst(Nat, z => {Nat.is_le(z, 1n+Nat.add(X, r)) == True{} : Bool}, 1n+p, Nat.add(p, 1n), Equal.sym(Nat, Nat.add(p, 1n), 1n+p, N.add_one(p)), hp)
      +h2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(1n+p, 1n), z) == True{} : Bool}, Nat.add(Nat.mul(1n+p, 2n), r), n, dm, h1)
      (N.le_zero_l(p), N.le_sub_r(1n+p, 1n, n, h2))

def HF(+n: Nat) -> Type:
  {Nat.is_le(1n, Nat.div(n, 2n)) == True{} : Bool} & {Nat.is_le(1n, Nat.sub(n, Nat.div(n, 2n))) == True{} : Bool}

def hf1(+n: Nat, r: HF(n)) -> {Nat.is_le(1n, Nat.div(n, 2n)) == True{} : Bool}:
  match r:
    case (x, y):
      x

def hf2(+n: Nat, r: HF(n)) -> {Nat.is_le(1n, Nat.sub(n, Nat.div(n, 2n))) == True{} : Bool}:
  match r:
    case (x, y):
      y

def half(+n: Nat, +h: {Nat.is_le(2n, n) == True{} : Bool}) -> HF(n):
  half.k(n, Nat.div(n, 2n), Nat.mod(n, 2n), N.div_mod(n, 2n), N.mod_lt(n, 2n, {==}), h)

def LP(+f: Nat, +c: String, +a: Nat, +b: Nat) -> Nat:
  List.length(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(b, a)), c, a, b))

def IHP(+f: Nat, +c: String) -> Type:
  @a2: Nat -> @b2: Nat -> {Nat.is_le(LP(f, c, a2, b2), max1(Nat.sub(b2, a2))) == True{} : Bool}

def pg0(+o: Bool, +c: String, +a: Nat, +b: Nat) ->
  {Nat.is_le(List.length(&2, Pr.Req, Norm.parts.go(0n, o, c, a, b)), max1(Nat.sub(b, a))) == True{} : Bool}:
  match o:
    case True{}:
      le1_max(Nat.sub(b, a))
    case False{}:
      le1_max(Nat.sub(b, a))

def pg.k(+f: Nat, +o: Bool, +c: String, +a: Nat, +b: Nat, +ho: {Norm.le31(Nat.sub(b, a)) == o : Bool}, ih1: IHP(f, c), ih2: IHP(f, c)) ->
  {Nat.is_le(List.length(&2, Pr.Req, Norm.parts.go(1n+f, o, c, a, b)), max1(Nat.sub(b, a))) == True{} : Bool}:
  match o:
    case True{}:
      le1_max(Nat.sub(b, a))
    case False{}:
      +n = Nat.sub(b, a)
      +dn = Nat.div(n, 2n)
      +m = Nat.add(a, dn)
      +ge = ge2(n, ho)
      +h1 = hf1(n, half(n, ge))
      +h2 = hf2(n, half(n, ge))
      +L1 = LP(f, c, a, m)
      +L2 = LP(f, c, m, b)
      +s1 = N.sub_add_l(a, dn)
      +s2 = Equal.sym(Nat, Nat.sub(n, dn), Nat.sub(b, m), S.sub_sub(b, a, dn))
      +i1 = AB.subst(Nat, z => {Nat.is_le(L1, z) == True{} : Bool}, max1(dn), dn, max1_eq(dn, h1),
        AB.subst(Nat, z => {Nat.is_le(L1, max1(z)) == True{} : Bool}, Nat.sub(m, a), dn, s1, ih1(a, m)))
      +i2 = AB.subst(Nat, z => {Nat.is_le(L2, z) == True{} : Bool}, max1(Nat.sub(n, dn)), Nat.sub(n, dn), max1_eq(Nat.sub(n, dn), h2),
        AB.subst(Nat, z => {Nat.is_le(L2, max1(z)) == True{} : Bool}, Nat.sub(b, m), Nat.sub(n, dn), s2, ih2(m, b)))
      +hs = P.le_add(L1, dn, L2, Nat.sub(n, dn), i1, i2)
      +hn = AB.subst(Nat, z => {Nat.is_le(Nat.add(L1, L2), z) == True{} : Bool}, Nat.add(dn, Nat.sub(n, dn)), n, N.le_sub_add(dn, n, sub_pos_le(n, dn, h2)), hs)
      +hm = AB.subst(Nat, z => {Nat.is_le(Nat.add(L1, L2), z) == True{} : Bool}, n, max1(n), Equal.sym(Nat, max1(n), n, max1_eq(n, N.le_trans(1n, 2n, n, {==}, ge))), hn)
      AB.subst(Nat, z => {Nat.is_le(z, max1(n)) == True{} : Bool}, Nat.add(L1, L2),
        List.length(&2, Pr.Req, List.append(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))),
        Equal.sym(Nat, List.length(&2, Pr.Req, List.append(&2, Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))), Nat.add(L1, L2),
          P.length_append(Pr.Req, Norm.parts.go(f, Norm.le31(Nat.sub(m, a)), c, a, m), Norm.parts.go(f, Norm.le31(Nat.sub(b, m)), c, m, b))),
        hm)

def pg_len(+fuel: Nat, +c: String, +a: Nat, +b: Nat) -> {Nat.is_le(LP(fuel, c, a, b), max1(Nat.sub(b, a))) == True{} : Bool}:
  match fuel:
    case 0n:
      pg0(Norm.le31(Nat.sub(b, a)), c, a, b)
    case 1n+f:
      pg.k(f, Norm.le31(Nat.sub(b, a)), c, a, b, {==}, a2 => b2 => pg_len(f, c, a2, b2), a2 => b2 => pg_len(f, c, a2, b2))

# parts(c, a, b) asks at most max(1, b - a) reads.
def parts_len(+c: String, +a: Nat, +b: Nat) -> {Nat.is_le(List.length(&2, Pr.Req, Norm.parts(c, a, b)), max1(Nat.sub(b, a))) == True{} : Bool}:
  pg_len(Nat.sub(b, a), c, a, b)

def rk(+o: Bool, +c: String, +a: Nat, +e: Nat, +a2: Nat, +e2: Nat) ->
  {Nat.is_le(List.length(&2, Pr.Req, Norm.Req.of.k(o, c, a, e, a2, e2)), max1(Nat.sub(e, a))) == True{} : Bool}:
  match o:
    case True{}:
      le1_max(Nat.sub(e, a))
    case False{}:
      parts_len(c, a, e)

# Req.of(c, a, e) asks one read, or parts(c, a, e): at most max(1, e - a).
def reqof_len(+c: String, +a: Nat, +e: Nat) -> {Nat.is_le(List.length(&2, Pr.Req, Norm.Req.of(c, a, e)), max1(Nat.sub(e, a))) == True{} : Bool}:
  +a2 = Nat.sub(a, Norm.margin())
  +e2 = Nat.max(e, Nat.add(a, Norm.ahead()))
  rk(Norm.le31(Nat.sub(e2, a2)), c, a, e, a2, e2)
