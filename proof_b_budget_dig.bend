import Base
import ./types.bend as B
import ./proof_b_cut_pos.bend as CP
import ./proof_base.bend as P
import lawful-fields@0.1.0.0/proof_num.bend as LN
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Number sizes for the output-length bound (notes/bytes_proofs_budget.md):
# a number below 10^k has at most 1 + k digits, a POS field of k characters
# reads as a number below 10^k, and linear bounds k * x + c as add chains.

# ---------------------------------------------------------------------------
# Linear bounds: LIN(k, c, x) = x + x + ... + x (k times) + c
# ---------------------------------------------------------------------------

def LIN(k: Nat, +c: Nat, +x: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+j:
      Nat.add(x, LIN(j, c, x))

def lin_succ(+k: Nat, +c: Nat, +x: Nat) -> {LIN(k, 1n+c, x) == 1n+LIN(k, c, x) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Nat, Nat.add(x, LIN(j, 1n+c, x)), Nat.add(x, 1n+LIN(j, c, x)), 1n+Nat.add(x, LIN(j, c, x)),
        Equal.cong(Nat, Nat, z => Nat.add(x, z), LIN(j, 1n+c, x), 1n+LIN(j, c, x), lin_succ(j, c, x)),
        N.add_succ(x, LIN(j, c, x)))

def lin_c(+c: Nat, +b: Nat, +d: Nat, +x: Nat) -> {Nat.add(c, LIN(b, d, x)) == LIN(b, Nat.add(c, d), x) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Nat, Nat.add(c, Nat.add(x, LIN(j, d, x))), Nat.add(x, Nat.add(c, LIN(j, d, x))), Nat.add(x, LIN(j, Nat.add(c, d), x)),
        N.add_left_comm(c, x, LIN(j, d, x)),
        Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(c, LIN(j, d, x)), LIN(j, Nat.add(c, d), x), lin_c(c, j, d, x)))

def lin_sum(+a: Nat, +c: Nat, +b: Nat, +d: Nat, +x: Nat) -> {Nat.add(LIN(a, c, x), LIN(b, d, x)) == LIN(Nat.add(a, b), Nat.add(c, d), x) : Nat}:
  match a:
    case 0n:
      lin_c(c, b, d, x)
    case 1n+j:
      Equal.trans(Nat, Nat.add(Nat.add(x, LIN(j, c, x)), LIN(b, d, x)), Nat.add(x, Nat.add(LIN(j, c, x), LIN(b, d, x))), Nat.add(x, LIN(Nat.add(j, b), Nat.add(c, d), x)),
        N.add_assoc(x, LIN(j, c, x), LIN(b, d, x)),
        Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(LIN(j, c, x), LIN(b, d, x)), LIN(Nat.add(j, b), Nat.add(c, d), x), lin_sum(j, c, b, d, x)))

# a <= LIN(k1, c1, x) and b <= LIN(k2, c2, x) give a + b <= LIN(k1 + k2, c1 + c2, x).
def lin_add(+a: Nat, +b: Nat, +k1: Nat, +c1: Nat, +k2: Nat, +c2: Nat, +x: Nat, +ha: {Nat.is_le(a, LIN(k1, c1, x)) == True{} : Bool}, +hb: {Nat.is_le(b, LIN(k2, c2, x)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, b), LIN(Nat.add(k1, k2), Nat.add(c1, c2), x)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(Nat.add(a, b), z) == True{} : Bool}, Nat.add(LIN(k1, c1, x), LIN(k2, c2, x)), LIN(Nat.add(k1, k2), Nat.add(c1, c2), x),
    lin_sum(k1, c1, k2, c2, x), N.le_trans(Nat.add(a, b), Nat.add(LIN(k1, c1, x), b), Nat.add(LIN(k1, c1, x), LIN(k2, c2, x)),
      N.le_add_mono_r(b, a, LIN(k1, c1, x), ha), N.le_add_mono_l(LIN(k1, c1, x), b, LIN(k2, c2, x), hb)))

# A part at most x is LIN(1, 0, x).
def lin_v(+a: Nat, +x: Nat, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(a, LIN(1n, 0n, x)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, x, Nat.add(x, 0n), Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x)), h)

def lin_k(+a: Nat, +c: Nat, +x: Nat, +h: {Nat.is_le(a, c) == True{} : Bool}) -> {Nat.is_le(a, LIN(0n, c, x)) == True{} : Bool}:
  h

def lin_le(+a: Nat, +k: Nat, +c: Nat, +k2: Nat, +c2: Nat, +x: Nat, +h: {Nat.is_le(a, LIN(k, c, x)) == True{} : Bool}, +hk: {Nat.is_le(LIN(k, c, x), LIN(k2, c2, x)) == True{} : Bool}) -> {Nat.is_le(a, LIN(k2, c2, x)) == True{} : Bool}:
  N.le_trans(a, LIN(k, c, x), LIN(k2, c2, x), h, hk)

# More of x or more constant is more.
def lin_mono(+k: Nat, +c: Nat, +k2: Nat, +c2: Nat, +x: Nat, +hk: {Nat.is_le(k, k2) == True{} : Bool}, +hc: {Nat.is_le(c, c2) == True{} : Bool}) -> {Nat.is_le(LIN(k, c, x), LIN(k2, c2, x)) == True{} : Bool}:
  match k k2:
    case 0n 0n:
      hc
    case 0n 1n+j:
      N.le_trans(c, LIN(j, c2, x), Nat.add(x, LIN(j, c2, x)), lin_mono(0n, c, j, c2, x, N.le_zero_l(j), hc), N.le_add_l(LIN(j, c2, x), x))
    case 1n+i 0n:
      Empty.absurd({Nat.is_le(LIN(1n+i, c, x), LIN(0n, c2, x)) == True{} : Bool}, N.false_ne_true(hk))
    case 1n+i 1n+j:
      N.le_add_mono_l(x, LIN(i, c, x), LIN(j, c2, x), lin_mono(i, c, j, c2, x, hk, hc))

def lin_x(+k: Nat, +c: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(LIN(k, c, x), LIN(k, c, y)) == True{} : Bool}:
  match k:
    case 0n:
      N.le_refl(c)
    case 1n+j:
      P.le_add(x, y, LIN(j, c, x), LIN(j, c, y), h, lin_x(j, c, x, y, h))

# ---------------------------------------------------------------------------
# Strings
# ---------------------------------------------------------------------------

def slen(+s: String) -> Nat:
  String.length(s)

def slen_app(a: String, +b: String) -> {String.length(a ++ b) == Nat.add(String.length(a), String.length(b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(Nat, Nat, z => 1n+z, String.length(t ++ b), Nat.add(String.length(t), String.length(b)), slen_app(t, b))

# ---------------------------------------------------------------------------
# Digits
# ---------------------------------------------------------------------------

def P10(k: Nat) -> Nat:
  Nat.pow(10n, k)

def p10_pos(+k: Nat) -> {Nat.is_le(1n, P10(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      N.le_trans(1n, P10(j), Nat.mul(10n, P10(j)), p10_pos(j), N.le_add_r(P10(j), Nat.mul(9n, P10(j))))

# A number below 10 has one digit.
def sh1(+n: Nat, +h: {Nat.is_lt(n, 10n) == True{} : Bool}) -> {Nat.is_le(String.length(Nat.show(n)), 1n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+k:
      Empty.absurd({Nat.is_le(String.length(Nat.show(10n+k)), 1n) == True{} : Bool},
        N.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(10n+k, 10n), False{}, Equal.sym(Bool, Nat.is_lt(10n+k, 10n), True{}, h), N.lt_add_self(10n, k))))

def IHD(+j: Nat) -> Type:
  @a: Nat -> {Nat.is_lt(a, P10(j)) == True{} : Bool} -> {Nat.is_le(String.length(Nat.show(a)), 1n+j) == True{} : Bool}

def dl.k(+j: Nat, +n: Nat, +a: Nat, +d: Nat, +e: {Nat.add(Nat.mul(a, 10n), d) == n : Nat}, +hd: {Nat.is_lt(d, 10n) == True{} : Bool},
  +h: {Nat.is_lt(n, P10(1n+j)) == True{} : Bool}, ih: IHD(j)) -> {Nat.is_le(String.length(Nat.show(n)), 1n+(1n+j)) == True{} : Bool}:
  match a:
    case 0n:
      +hn = AB.subst(Nat, z => {Nat.is_lt(z, 10n) == True{} : Bool}, d, n, e, hd)
      N.le_trans(String.length(Nat.show(n)), 1n, 2n+j, sh1(n, hn), N.le_zero_l(1n+j))
    case 1n+p:
      +A = {1n+p : Nat}
      +es = AB.subst(Nat, z => {Nat.show(z) == Nat.show(A) ++ CP.DCH(d) : String}, Nat.add(Nat.mul(A, 10n), d), n, e, CP.show_snoc(A, d, N.le_zero_l(p), hd))
      +hA0 = N.le_lt_trans(Nat.mul(A, 10n), n, P10(1n+j),
        AB.subst(Nat, z => {Nat.is_le(Nat.mul(A, 10n), z) == True{} : Bool}, Nat.add(Nat.mul(A, 10n), d), n, e, N.le_add_r(Nat.mul(A, 10n), d)), h)
      +hA1 = AB.subst(Nat, z => {Nat.is_lt(z, Nat.mul(10n, P10(j))) == True{} : Bool}, Nat.mul(A, 10n), Nat.mul(10n, A), N.mul_comm(A, 10n), hA0)
      +hA = N.lt_mul_cancel(10n, A, P10(j), hA1)
      +l1 = AB.subst(Nat, z => {Nat.is_le(z, 1n+(1n+j)) == True{} : Bool}, Nat.add(String.length(Nat.show(A)), 1n), String.length(Nat.show(A) ++ CP.DCH(d)),
        Equal.sym(Nat, String.length(Nat.show(A) ++ CP.DCH(d)), Nat.add(String.length(Nat.show(A)), 1n), slen_app(Nat.show(A), CP.DCH(d))),
        AB.subst(Nat, z => {Nat.is_le(z, 1n+(1n+j)) == True{} : Bool}, 1n+String.length(Nat.show(A)), Nat.add(String.length(Nat.show(A)), 1n),
          Equal.sym(Nat, Nat.add(String.length(Nat.show(A)), 1n), 1n+String.length(Nat.show(A)), N.add_one(String.length(Nat.show(A)))), ih(A, hA)))
      AB.subst(String, z => {Nat.is_le(String.length(z), 1n+(1n+j)) == True{} : Bool}, Nat.show(A) ++ CP.DCH(d), Nat.show(n),
        Equal.sym(String, Nat.show(n), Nat.show(A) ++ CP.DCH(d), es), l1)

# A number below 10^k has at most 1 + k digits.
def dlen(+k: Nat, +n: Nat, +h: {Nat.is_lt(n, P10(k)) == True{} : Bool}) -> {Nat.is_le(String.length(Nat.show(n)), 1n+k) == True{} : Bool}:
  match k:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+m:
          Empty.absurd({Nat.is_le(String.length(Nat.show(1n+m)), 1n) == True{} : Bool},
            N.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(1n+m, 1n), False{}, Equal.sym(Bool, Nat.is_lt(1n+m, 1n), True{}, h), N.lt_add_self(1n, m))))
    case 1n+j:
      dl.k(j, n, Nat.div(n, 10n), Nat.mod(n, 10n), N.div_mod(n, 10n), N.mod_lt(n, 10n, {==}), h, a => ha => dlen(j, a, ha))

# x < 10^k gives x + r < 10^(r + k).
def lt_pow_add(+x: Nat, +k: Nat, +r: Nat, +h: {Nat.is_lt(x, P10(k)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x, r), P10(Nat.add(r, k))) == True{} : Bool}:
  match r:
    case 0n:
      AB.subst(Nat, z => {Nat.is_lt(z, P10(k)) == True{} : Bool}, x, Nat.add(x, 0n), Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x)), h)
    case 1n+j:
      +y = Nat.add(x, j)
      +Q = P10(Nat.add(j, k))
      +ih = lt_pow_add(x, k, j, h)
      +h1 = Equal.trans(Bool, Nat.is_le(1n+y, Q), Nat.is_lt(y, Q), True{}, N.le_succ_lt(y, Q), ih)
      +q1 = N.le_trans(1n, 1n+y, Q, N.le_zero_l(y), h1)
      +h2 = N.le_trans(2n+y, Nat.add(Q, 1n), Nat.add(Q, Q), AB.subst(Nat, z => {Nat.is_le(2n+y, z) == True{} : Bool}, 1n+Q, Nat.add(Q, 1n), Equal.sym(Nat, Nat.add(Q, 1n), 1n+Q, N.add_one(Q)), h1),
        N.le_add_mono_l(Q, 1n, Q, q1))
      +h3 = N.le_trans(2n+y, Nat.add(Q, Q), Nat.mul(10n, Q), h2, N.le_add_mono_l(Q, Q, Nat.mul(9n, Q), N.le_add_r(Q, Nat.mul(8n, Q))))
      +h4 = Equal.trans(Bool, Nat.is_lt(1n+y, Nat.mul(10n, Q)), Nat.is_le(2n+y, Nat.mul(10n, Q)), True{}, Equal.sym(Bool, Nat.is_le(2n+y, Nat.mul(10n, Q)), Nat.is_lt(1n+y, Nat.mul(10n, Q)), N.le_succ_lt(1n+y, Nat.mul(10n, Q))), h3)
      AB.subst(Nat, z => {Nat.is_lt(z, Nat.mul(10n, Q)) == True{} : Bool}, 1n+y, Nat.add(x, 1n+j), Equal.sym(Nat, Nat.add(x, 1n+j), 1n+y, N.add_succ(x, j)), h4)

# ---------------------------------------------------------------------------
# POS: a field of k characters reads as a number below 10^k
# ---------------------------------------------------------------------------

def DV(m: Maybe<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, m, 0n)

def none_some(+k: Nat, +e: {None{} == Some{k} : Maybe<&2, Nat>}) -> Empty:
  N.false_ne_true(Equal.cong(Maybe<&2, Nat>, Bool, m => Maybe.is_some(&2, Nat, m), None{}, Some{k}, e))

def digit_le9.if(+x: U32, b: Bool, +eb: {Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)) == b : Bool}, +k: Nat,
  +e: {B.Pos.digit.if(x, b) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_le(k, 9n) == True{} : Bool}:
  match b:
    case False{}:
      Empty.absurd({Nat.is_le(k, 9n) == True{} : Bool}, none_some(k, e))
    case True{}:
      +ek = Equal.cong(Maybe<&2, Nat>, Nat, m => DV(m), Some{U32.to_nat(U32.sub(x, 48))}, Some{k}, e)
      +hge = N.and_true_l(U32.is_ge(x, 48), U32.is_le(x, 57), eb)
      +hle = N.and_true_r(U32.is_ge(x, 48), U32.is_le(x, 57), eb)
      +es = U.to_nat_sub_le(x, 48, LN.le48(x, hge))
      AB.subst(Nat, z => {Nat.is_le(z, 9n) == True{} : Bool}, Nat.sub(U32.to_nat(x), 48n), k,
        Equal.trans(Nat, Nat.sub(U32.to_nat(x), 48n), U32.to_nat(U32.sub(x, 48)), k, Equal.sym(Nat, U32.to_nat(U32.sub(x, 48)), Nat.sub(U32.to_nat(x), 48n), es), ek),
        LN.k9(x, hle))

def digit_le9(+c: Char, +k: Nat, +e: {B.Pos.digit(c) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_le(k, 9n) == True{} : Bool}:
  match c:
    case Chr{+x}:
      digit_le9.if(x, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), {==}, k, e)

def go_none(s: String) -> {B.Pos.read.go(s, None{}) == None{} : Maybe<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      go_none(t)

def zero_lt(+k: Nat, +n: Nat) -> {Nat.is_lt(0n, Nat.mul(1n+n, P10(k))) == True{} : Bool}:
  N.lt_le_trans(0n, 1n, Nat.mul(1n+n, P10(k)), {==}, N.le_trans(1n, P10(k), Nat.mul(1n+n, P10(k)), p10_pos(k), N.le_add_r(P10(k), Nat.mul(n, P10(k)))))

def IHR(t: String) -> Type:
  @acc: Maybe<&2, Nat> -> {Nat.is_lt(DV(B.Pos.read.go(t, acc)), Nat.mul(1n+DV(acc), P10(String.length(t)))) == True{} : Bool}

def pr.k(+h: Char, +t: String, +a: Nat, x: Maybe<&2, Nat>, +ex: {B.Pos.digit(h) == x : Maybe<&2, Nat>}, ih: IHR(t)) ->
  {Nat.is_lt(DV(B.Pos.read.go(t, B.Pos.read.push(Some{a}, x))), Nat.mul(1n+a, P10(1n+String.length(t)))) == True{} : Bool}:
  match x:
    case None{}:
      AB.subst(Maybe<&2, Nat>, z => {Nat.is_lt(DV(z), Nat.mul(1n+a, P10(1n+String.length(t)))) == True{} : Bool}, None{}, B.Pos.read.go(t, None{}),
        Equal.sym(Maybe<&2, Nat>, B.Pos.read.go(t, None{}), None{}, go_none(t)), zero_lt(1n+String.length(t), a))
    case Some{+k}:
      +P = P10(String.length(t))
      +X = Nat.mul(a, 10n)
      +v = Nat.add(X, k)
      +h9 = digit_le9(h, k, ex)
      +H1 = AB.subst(Nat, z => {Nat.is_le(1n+z, Nat.add(10n, X)) == True{} : Bool}, Nat.add(k, X), v, N.add_comm(k, X),
        N.le_add_mono_r(X, 1n+k, 10n, h9))
      +H2 = N.le_mul_r(1n+v, Nat.mul(1n+a, 10n), P, H1)
      +H3 = AB.subst(Nat, z => {Nat.is_le(Nat.mul(1n+v, P), z) == True{} : Bool}, Nat.mul(Nat.mul(1n+a, 10n), P), Nat.mul(1n+a, Nat.mul(10n, P)),
        N.mul_assoc(1n+a, 10n, P), H2)
      N.lt_le_trans(DV(B.Pos.read.go(t, Some{v})), Nat.mul(1n+v, P), Nat.mul(1n+a, Nat.mul(10n, P)), ih(Some{v}), H3)

def pr.c(+h: Char, +t: String, +acc: Maybe<&2, Nat>, ih: IHR(t)) ->
  {Nat.is_lt(DV(B.Pos.read.go(SCon{h, t}, acc)), Nat.mul(1n+DV(acc), P10(1n+String.length(t)))) == True{} : Bool}:
  match acc:
    case None{}:
      AB.subst(Maybe<&2, Nat>, z => {Nat.is_lt(DV(z), Nat.mul(1n, P10(1n+String.length(t)))) == True{} : Bool}, None{}, B.Pos.read.go(t, B.Pos.read.push(None{}, B.Pos.digit(h))),
        Equal.sym(Maybe<&2, Nat>, B.Pos.read.go(t, None{}), None{}, go_none(t)), zero_lt(1n+String.length(t), 0n))
    case Some{+a}:
      pr.k(h, t, a, B.Pos.digit(h), {==}, ih)

def pr_go(+s: String, +acc: Maybe<&2, Nat>) -> {Nat.is_lt(DV(B.Pos.read.go(s, acc)), Nat.mul(1n+DV(acc), P10(String.length(s)))) == True{} : Bool}:
  match s:
    case SNil{}:
      +D = DV(acc)
      Equal.trans(Bool, Nat.is_lt(D, 1n+Nat.mul(D, 1n)), Nat.is_le(D, Nat.mul(D, 1n)), True{}, N.lt_succ_iff(D, Nat.mul(D, 1n)),
        AB.subst(Nat, z => {Nat.is_le(D, z) == True{} : Bool}, D, Nat.mul(D, 1n), Equal.sym(Nat, Nat.mul(D, 1n), D, N.mul_one(D)), N.le_refl(D)))
    case SCon{+h, +t}:
      pr.c(h, t, acc, a2 => pr_go(t, a2))

# A field of k characters reads as a number below 10^k (0 if it is no number).
def pos_lt(+s: String) -> {Nat.is_lt(DV(B.Pos.read(s)), P10(String.length(s))) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      +P = P10(1n+String.length(t))
      AB.subst(Nat, z => {Nat.is_lt(DV(B.Pos.read.go(SCon{h, t}, Some{0n})), z) == True{} : Bool}, Nat.add(P, 0n), P, N.add_zero(P),
        pr_go(SCon{h, t}, Some{0n}))

# A number at most p + r, with p below 10^k, has at most 1 + r + k digits.
def qdig(+p: Nat, +r: Nat, +k: Nat, +q: Nat, +hp: {Nat.is_lt(p, P10(k)) == True{} : Bool}, +hq: {Nat.is_le(q, Nat.add(p, r)) == True{} : Bool}) ->
  {Nat.is_le(String.length(Nat.show(q)), 1n+Nat.add(r, k)) == True{} : Bool}:
  dlen(Nat.add(r, k), q, N.le_lt_trans(q, Nat.add(p, r), P10(Nat.add(r, k)), hq, lt_pow_add(p, k, r, hp)))
