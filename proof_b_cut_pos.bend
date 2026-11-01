import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_nat.bend as Z
import ./proof_b_cut_str.bend as S
import ./proof_run_dec.bend as RD
import ./proof_run_base.bend as RB
import ./proof_base.bend as P
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_find.bend as PF
import lawful-bytes@0.1.1.0/proof_append.bend as PA
import lawful-bytes@0.1.1.0/proof_seq.bend as PSq
import lawful-fields@0.1.1.0/proof_num.bend as LN
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# POS: what NF.num reads is the number the digits stand for (no overflow:
# at most 9 digits, each step bounded by a word constant 9 .. 999999999),
# and Nat.show writes it back as the same digits (no leading zero).

# ---------------------------------------------------------------------------
# Digits as a list
# ---------------------------------------------------------------------------

def alld(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      NF.is_digit(x) && alld(t)

# The value of the digits after v.
def valn(xs: List<&2, U32>, +v: Nat) -> Nat:
  match xs:
    case Nil{}:
      v
    case Con{+x, t}:
      valn(t, Nat.add(Nat.mul(v, 10n), Nat.sub(U32.to_nat(x), 48n)))

# 10^J - 1 as a word.
def PK(J: Nat) -> U32:
  match J:
    case 0n:
      0
    case 1n+i:
      ((PK(i) * 10 : U32) + 9 : U32)

def pk_lt(+J: Nat, +h: {Nat.is_le(J, 8n) == True{} : Bool}) -> {U32.is_lt(PK(J), 429496729) == True{} : Bool}:
  match J:
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
    case 9n+k:
      Empty.absurd({U32.is_lt(PK(9n+k), 429496729) == True{} : Bool}, N.false_ne_true(h))

def u_le_lt(+a: U32, +b: U32, +c: U32, +h1: {U32.is_le(a, b) == True{} : Bool}, +h2: {U32.is_lt(b, c) == True{} : Bool}) ->
  {U32.is_lt(a, c) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(a, c), Nat.is_lt(U32.to_nat(a), U32.to_nat(c)), True{}, U.is_lt_to_nat(a, c),
    N.le_lt_trans(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c), Z.ule(a, b, h1),
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(b), U32.to_nat(c)), U32.is_lt(b, c), True{}, Equal.sym(Bool, U32.is_lt(b, c), Nat.is_lt(U32.to_nat(b), U32.to_nat(c)), U.is_lt_to_nat(b, c)), h2)))

# No overflow while acc is below 429496729.
def fit(+acc: U32, +x: U32, +M: Nat, +q: Nat, +hcq: {U32.to_nat(429496729) == q : Nat}, +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat},
  +hge: {U32.is_ge(x, 48) == True{} : Bool}, +hle: {U32.is_le(x, 57) == True{} : Bool}, +hlt: {U32.is_lt(acc, 429496729) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), M) == True{} : Bool}:
  +f = LN.FITSU(acc, x, 429496729, q, M, hcq, hq, hge, hle)
  Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), M),
    Bool.or(U32.is_lt(acc, 429496729), Bool.and(U32.is_eq(acc, 429496729), U32.is_le(U32.sub(x, 48), 5))), True{},
    Equal.sym(Bool, Bool.or(U32.is_lt(acc, 429496729), Bool.and(U32.is_eq(acc, 429496729), U32.is_le(U32.sub(x, 48), 5))), Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), M), f),
    AB.subst(Bool, z => {Bool.or(z, Bool.and(U32.is_eq(acc, 429496729), U32.is_le(U32.sub(x, 48), 5))) == True{} : Bool}, True{}, U32.is_lt(acc, 429496729),
      Equal.sym(Bool, U32.is_lt(acc, 429496729), True{}, hlt), {==}))

def stp_v(+acc: U32, +x: U32, +J: Nat, +M: Nat, +q: Nat, +hm: {Nat.pow(2n, 32n) == M : Nat}, +hcq: {U32.to_nat(429496729) == q : Nat},
  +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}, +hJ: {Nat.is_le(J, 8n) == True{} : Bool}, +hacc: {U32.is_le(acc, PK(J)) == True{} : Bool},
  +hge: {U32.is_ge(x, 48) == True{} : Bool}, +hle: {U32.is_le(x, 57) == True{} : Bool}) ->
  {U32.to_nat(LN.NA(acc, x)) == Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)) : Nat}:
  LN.ena(acc, x, M, hm, hge, fit(acc, x, M, q, hcq, hq, hge, hle, u_le_lt(acc, PK(J), 429496729, hacc, pk_lt(J, hJ))))

def stp_b(+acc: U32, +x: U32, +J: Nat, +M: Nat, +q: Nat, +hm: {Nat.pow(2n, 32n) == M : Nat}, +hcq: {U32.to_nat(429496729) == q : Nat},
  +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}, +hJ: {Nat.is_le(J, 8n) == True{} : Bool}, +hacc: {U32.is_le(acc, PK(J)) == True{} : Bool},
  +hge: {U32.is_ge(x, 48) == True{} : Bool}, +hle: {U32.is_le(x, 57) == True{} : Bool}) ->
  {U32.is_le(LN.NA(acc, x), LN.NA(PK(J), 57)) == True{} : Bool}:
  +A = U32.to_nat(acc)
  +P = U32.to_nat(PK(J))
  +D9 = {9n : Nat}
  +Dx = Nat.sub(U32.to_nat(x), 48n)
  +ev = stp_v(acc, x, J, M, q, hm, hcq, hq, hJ, hacc, hge, hle)
  +ep = AB.subst(Nat, z => {U32.to_nat(LN.NA(PK(J), 57)) == Nat.add(Nat.mul(P, 10n), z) : Nat}, Nat.sub(U32.to_nat(57), 48n), 9n, {==},
    LN.ena(PK(J), 57, M, hm, {==}, fit(PK(J), 57, M, q, hcq, hq, {==}, {==}, pk_lt(J, hJ))))
  +hle2 = P.le_add(Nat.mul(A, 10n), Nat.mul(P, 10n), Dx, D9, N.le_mul_r(A, P, 10n, Z.ule(acc, PK(J), hacc)), LN.k9(x, hle))
  +h3 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.mul(P, 10n), D9)) == True{} : Bool}, Nat.add(Nat.mul(A, 10n), Dx), U32.to_nat(LN.NA(acc, x)), Equal.sym(Nat, U32.to_nat(LN.NA(acc, x)), Nat.add(Nat.mul(A, 10n), Dx), ev), hle2)
  +h4 = AB.subst(Nat, z => {Nat.is_le(U32.to_nat(LN.NA(acc, x)), z) == True{} : Bool}, Nat.add(Nat.mul(P, 10n), D9), U32.to_nat(LN.NA(PK(J), 57)), Equal.sym(Nat, U32.to_nat(LN.NA(PK(J), 57)), Nat.add(Nat.mul(P, 10n), D9), ep), h3)
  Z.nle(LN.NA(acc, x), LN.NA(PK(J), 57), h4)

def stp_b1(+acc: U32, +x: U32, +J: Nat, +M: Nat, +q: Nat, +hm: {Nat.pow(2n, 32n) == M : Nat}, +hcq: {U32.to_nat(429496729) == q : Nat},
  +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}, +hJ: {Nat.is_le(J, 8n) == True{} : Bool}, +hacc: {U32.is_le(acc, PK(J)) == True{} : Bool},
  +hge: {U32.is_ge(x, 48) == True{} : Bool}, +hle: {U32.is_le(x, 57) == True{} : Bool}) ->
  {U32.is_le(LN.NA(acc, x), PK(1n+J)) == True{} : Bool}:
  stp_b(acc, x, J, M, q, hm, hcq, hq, hJ, hacc, hge, hle)

# ---------------------------------------------------------------------------
# num's loop (M.NG) on the digits
# ---------------------------------------------------------------------------

def ng_ok(+m: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +j: U32, +acc: U32, +ok: Bool,
  +h: {M.Nv.ok(M.NG(m, len, t, x, j, acc, ok)) == True{} : Bool}) -> {ok == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+k:
      N.and_true_l(ok, NF.is_digit(x), ng_ok(k, len, t, C.AT(len, t, (j + 1 : U32)), (j + 1 : U32), LN.NA(acc, x), ok && NF.is_digit(x), h))

def ng_dx(+k: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +j: U32, +acc: U32, +ok: Bool,
  +h: {M.Nv.ok(M.NG(1n+k, len, t, x, j, acc, ok)) == True{} : Bool}) -> {NF.is_digit(x) == True{} : Bool}:
  N.and_true_r(ok, NF.is_digit(x), ng_ok(k, len, t, C.AT(len, t, (j + 1 : U32)), (j + 1 : U32), LN.NA(acc, x), ok && NF.is_digit(x), h))

def slice0(+xs: List<&2, U32>, +a: Nat) -> {D.slice(xs, a, 0n) == Nil{} : List<&2, U32>}:
  PSq.take_zero(List.drop(&2, U32, xs, a))

# One step: the slice from j starts with byte j, and j + 1 is one past it.
def SLC(+len: U32, +t: AT.Tree<U32>, +j: U32, +k: Nat) -> Type:
  {D.slice(Z.X(len, t), Z.n(j), 1n+k) == C.AT(len, t, j) <> D.slice(Z.X(len, t), Z.n((j + 1 : U32)), k) : List<&2, U32>}

def slc(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +k: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hp: {Nat.is_le(Nat.add(Z.n(j), 1n+k), Z.n(len)) == True{} : Bool}) -> SLC(len, t, j, k):
  +hj = N.lt_le_trans(Z.n(j), Nat.add(Z.n(j), 1n+k), Z.n(len), PF.lt_add_succ(Z.n(j), k), hp)
  +inc = Z.nx1(len, j, Z.nxt(len, t, d, j, hok, hj))
  AB.subst(Nat, z => {D.slice(Z.X(len, t), Z.n(j), 1n+k) == C.AT(len, t, j) <> D.slice(Z.X(len, t), z, k) : List<&2, U32>}, Nat.add(Z.n(j), 1n), Z.n((j + 1 : U32)),
    Equal.sym(Nat, Z.n((j + 1 : U32)), Nat.add(Z.n(j), 1n), inc), PA.slice_cons(Z.X(len, t), Z.n(j), k, C.AT(len, t, j), PF.step_get(len, t, d, j, hok, hj)))

def hp_next(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +k: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hp: {Nat.is_le(Nat.add(Z.n(j), 1n+k), Z.n(len)) == True{} : Bool}) -> {Nat.is_le(Nat.add(Z.n((j + 1 : U32)), k), Z.n(len)) == True{} : Bool}:
  +hj = N.lt_le_trans(Z.n(j), Nat.add(Z.n(j), 1n+k), Z.n(len), PF.lt_add_succ(Z.n(j), k), hp)
  +inc = Z.nx1(len, j, Z.nxt(len, t, d, j, hok, hj))
  AB.subst(Nat, z => {Nat.is_le(Nat.add(z, k), Z.n(len)) == True{} : Bool}, Nat.add(Z.n(j), 1n), Z.n((j + 1 : U32)), Equal.sym(Nat, Z.n((j + 1 : U32)), Nat.add(Z.n(j), 1n), inc),
    AB.subst(Nat, z => {Nat.is_le(z, Z.n(len)) == True{} : Bool}, Nat.add(Z.n(j), 1n+k), Nat.add(Nat.add(Z.n(j), 1n), k), Equal.sym(Nat, Nat.add(Nat.add(Z.n(j), 1n), k), Nat.add(Z.n(j), 1n+k), N.add_assoc(Z.n(j), 1n, k)), hp))

# The bytes num read are digits.
def ng_dig(+m: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +x: U32, +j: U32, +acc: U32, +ok: Bool, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h: {M.Nv.ok(M.NG(m, len, t, x, j, acc, ok)) == True{} : Bool}, +hx: {x == C.AT(len, t, j) : U32},
  +hp: {Nat.is_le(Nat.add(Z.n(j), m), Z.n(len)) == True{} : Bool}) -> {alld(D.slice(Z.X(len, t), Z.n(j), m)) == True{} : Bool}:
  match m:
    case 0n:
      %Equal.sym(List<&2, U32>, D.slice(Z.X(len, t), Z.n(j), 0n), Nil{}, slice0(Z.X(len, t), Z.n(j))) : {alld(_) == True{} : Bool}
      {==}
    case 1n+k:
      +y = C.AT(len, t, (j + 1 : U32))
      +ih = ng_dig(k, len, t, d, y, (j + 1 : U32), LN.NA(acc, x), ok && NF.is_digit(x), hok, h, {==}, hp_next(len, t, d, j, k, hok, hp))
      +dx = AB.subst(U32, z => {NF.is_digit(z) == True{} : Bool}, x, C.AT(len, t, j), hx, ng_dx(k, len, t, x, j, acc, ok, h))
      %Equal.sym(List<&2, U32>, D.slice(Z.X(len, t), Z.n(j), 1n+k), C.AT(len, t, j) <> D.slice(Z.X(len, t), Z.n((j + 1 : U32)), k), slc(len, t, d, j, k, hok, hp)) :
        {alld(_) == True{} : Bool}
      %Equal.sym(Bool, NF.is_digit(C.AT(len, t, j)), True{}, dx) : {(_ && alld(D.slice(Z.X(len, t), Z.n((j + 1 : U32)), k))) == True{} : Bool}
      ih

# The number num read is the value of the digits.
def ng_v(+m: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +x: U32, +j: U32, +acc: U32, +ok: Bool, +J: Nat, +M: Nat, +q: Nat,
  +hm: {Nat.pow(2n, 32n) == M : Nat}, +hcq: {U32.to_nat(429496729) == q : Nat}, +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h: {M.Nv.ok(M.NG(m, len, t, x, j, acc, ok)) == True{} : Bool}, +hx: {x == C.AT(len, t, j) : U32},
  +hp: {Nat.is_le(Nat.add(Z.n(j), m), Z.n(len)) == True{} : Bool}, +hJ: {Nat.is_le(Nat.add(J, m), 9n) == True{} : Bool},
  +hacc: {U32.is_le(acc, PK(J)) == True{} : Bool}, +v: Nat, +hv: {U32.to_nat(acc) == v : Nat}) ->
  {U32.to_nat(M.Nv.v(M.NG(m, len, t, x, j, acc, ok))) == valn(D.slice(Z.X(len, t), Z.n(j), m), v) : Nat}:
  match m:
    case 0n:
      %Equal.sym(List<&2, U32>, D.slice(Z.X(len, t), Z.n(j), 0n), Nil{}, slice0(Z.X(len, t), Z.n(j))) : {U32.to_nat(acc) == valn(_, v) : Nat}
      hv
    case 1n+k:
      +dx = ng_dx(k, len, t, x, j, acc, ok, h)
      +hge = N.and_true_l(U32.is_ge(x, 48), U32.is_le(x, 57), dx)
      +hle = N.and_true_r(U32.is_ge(x, 48), U32.is_le(x, 57), dx)
      +hJs = AB.subst(Nat, z => {Nat.is_le(z, 9n) == True{} : Bool}, Nat.add(J, 1n+k), 1n+Nat.add(J, k), N.add_succ(J, k), hJ)
      +hJ8 = N.le_trans(J, Nat.add(J, k), 8n, N.le_add_r(J, k), hJs)
      +v2 = Nat.add(Nat.mul(v, 10n), Nat.sub(U32.to_nat(x), 48n))
      +hv2 = Equal.trans(Nat, U32.to_nat(LN.NA(acc, x)), Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), v2,
        stp_v(acc, x, J, M, q, hm, hcq, hq, hJ8, hacc, hge, hle),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, 10n), Nat.sub(U32.to_nat(x), 48n)), U32.to_nat(acc), v, hv))
      +ih = ng_v(k, len, t, d, C.AT(len, t, (j + 1 : U32)), (j + 1 : U32), LN.NA(acc, x), ok && NF.is_digit(x), 1n+J, M, q, hm, hcq, hq, hok, h, {==},
        hp_next(len, t, d, j, k, hok, hp), hJs, stp_b1(acc, x, J, M, q, hm, hcq, hq, hJ8, hacc, hge, hle), v2, hv2)
      +S2 = D.slice(Z.X(len, t), Z.n((j + 1 : U32)), k)
      +L = U32.to_nat(M.Nv.v(M.NG(1n+k, len, t, x, j, acc, ok)))
      %Equal.sym(List<&2, U32>, D.slice(Z.X(len, t), Z.n(j), 1n+k), C.AT(len, t, j) <> S2, slc(len, t, d, j, k, hok, hp)) : {L == valn(_, v) : Nat}
      AB.subst(U32, z => {L == valn(S2, Nat.add(Nat.mul(v, 10n), Nat.sub(U32.to_nat(z), 48n))) : Nat}, x, C.AT(len, t, j), hx, ih)

def min_le(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.min(1n+p, 0n) == 1n+p : Nat}, N.false_ne_true(h))
    case 1n+p 1n+r:
      %Equal.sym(Nat, Nat.min(p, r), p, min_le(p, r, h)) : {1n+_ == 1n+p : Nat}
      {==}

# POS from .. to-1 as num reads it.
def NOK0(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) -> Bool:
  U32.is_le(1, (to - from : U32)) && U32.is_le((to - from : U32), 9) && Bool.not(U32.is_eq(C.AT(len, t, from), 48))

def nok0(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +h: {M.Nv.ok(M.NUM(len, t, from, to)) == True{} : Bool}) ->
  {NOK0(len, t, from, to) == True{} : Bool}:
  ng_ok(U32.to_nat(U32.min((to - from : U32), 10)), len, t, C.AT(len, t, from), from, 0, NOK0(len, t, from, to), h)

def fuel_eq(+nn: U32, +h: {U32.is_le(nn, 9) == True{} : Bool}) -> {U32.to_nat(U32.min(nn, 10)) == U32.to_nat(nn) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.min(nn, 10)), Nat.min(U32.to_nat(nn), U32.to_nat(10)), U32.to_nat(nn), U.to_nat_min(nn, 10),
    min_le(U32.to_nat(nn), U32.to_nat(10), N.le_trans(U32.to_nat(nn), U32.to_nat(9), U32.to_nat(10), Z.ule(nn, 9, h), {==})))

# ---------------------------------------------------------------------------
# The digits as text: B.Pos.read and Nat.show
# ---------------------------------------------------------------------------

def pr_go(xs: List<&2, U32>, +v: Nat, +hd: {alld(xs) == True{} : Bool}) ->
  {B.Pos.read.go(Norm.chars(xs), Some{v}) == Some{valn(xs, v)} : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +dy = N.and_true_l(NF.is_digit(y), alld(t), hd)
      +hge = N.and_true_l(U32.is_ge(y, 48), U32.is_le(y, 57), dy)
      +v2 = Nat.add(Nat.mul(v, 10n), Nat.sub(U32.to_nat(y), 48n))
      %Equal.sym(Bool, U32.is_ge(y, 48) && U32.is_le(y, 57), True{}, dy) :
        {B.Pos.read.go(Norm.chars(t), B.Pos.read.push(Some{v}, B.Pos.digit.if(y, _))) == Some{valn(t, v2)} : Maybe<&2, Nat>}
      %Equal.sym(Nat, U32.to_nat(U32.sub(y, 48)), Nat.sub(U32.to_nat(y), 48n), LN.ed48(y, hge)) :
        {B.Pos.read.go(Norm.chars(t), Some{Nat.add(Nat.mul(v, 10n), _)}) == Some{valn(t, v2)} : Maybe<&2, Nat>}
      pr_go(t, v2, N.and_true_r(NF.is_digit(y), alld(t), hd))

def show_small(+r: Nat, +h: {Nat.is_le(r, 9n) == True{} : Bool}) -> {Nat.show(r) == SCon{Chr{U32.from_nat(Nat.add(48n, r))}, SNil{}} : String}:
  match r:
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
      Empty.absurd({Nat.show(10n+k) == SCon{Chr{U32.from_nat(Nat.add(48n, 10n+k))}, SNil{}} : String}, N.false_ne_true(h))

def lt_s9(+z: Nat) -> {Nat.is_lt(z, 9n+z) == True{} : Bool}:
  match z:
    case 0n:
      {==}
    case 1n+w:
      lt_s9(w)

def lt_m10(+p: Nat, +rr: Nat) -> {Nat.is_lt(1n+p, Nat.add(Nat.mul(1n+p, 10n), rr)) == True{} : Bool}:
  +Z = Nat.add(Nat.mul(p, 10n), rr)
  N.le_lt_trans(p, Z, 9n+Z, N.le_trans(p, Nat.mul(p, 10n), Z, RD.le_mul10(p), N.le_add_r(Nat.mul(p, 10n), rr)), lt_s9(Z))

def divlt(+n: Nat, +p: Nat, +hQ: {Nat.div(n, 10n) == 1n+p : Nat}) -> {Nat.is_lt(1n+p, n) == True{} : Bool}:
  +md = Nat.mod(n, 10n)
  +eq = AB.subst(Nat, z => {Nat.add(Nat.mul(z, 10n), md) == n : Nat}, Nat.div(n, 10n), 1n+p, hQ, N.div_mod(n, 10n))
  AB.subst(Nat, z => {Nat.is_lt(1n+p, z) == True{} : Bool}, Nat.add(Nat.mul(1n+p, 10n), md), n, eq, lt_m10(p, md))

def FG(+g1: Nat, +g2: Nat) -> Type:
  @n2: Nat -> @a2: String -> {Nat.is_lt(n2, g1) == True{} : Bool} -> {Nat.is_lt(n2, g2) == True{} : Bool} -> {Nat.show.go(g1, n2, a2) == Nat.show.go(g2, n2, a2) : String}

def fi.k(+g1: Nat, +g2: Nat, +n: Nat, +acc: String, +Q: Nat, +hQ: {Nat.div(n, 10n) == Q : Nat},
  +hn1: {Nat.is_le(n, g1) == True{} : Bool}, +hn2: {Nat.is_le(n, g2) == True{} : Bool}, ih: FG(g1, g2)) ->
  {Nat.show.fin(g1, acc, (Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Q)) == Nat.show.fin(g2, acc, (Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Q)) : String}:
  match Q:
    case 0n:
      {==}
    case 1n+p:
      +hl = divlt(n, p, hQ)
      ih(1n+p, SCon{Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, acc}, N.lt_le_trans(1n+p, n, g1, hl, hn1), N.lt_le_trans(1n+p, n, g2, hl, hn2))

# Nat.show's fuel only has to exceed the number.
def go_fuel(+f1: Nat, +f2: Nat, +n: Nat, +acc: String, +h1: {Nat.is_lt(n, f1) == True{} : Bool}, +h2: {Nat.is_lt(n, f2) == True{} : Bool}) ->
  {Nat.show.go(f1, n, acc) == Nat.show.go(f2, n, acc) : String}:
  match f1 f2:
    case 0n _:
      Empty.absurd({Nat.show.go(0n, n, acc) == Nat.show.go(f2, n, acc) : String}, Z.ne_tf(Nat.is_lt(n, 0n), h1, N.lt_zero(n)))
    case 1n+g1 0n:
      Empty.absurd({Nat.show.go(1n+g1, n, acc) == Nat.show.go(0n, n, acc) : String}, Z.ne_tf(Nat.is_lt(n, 0n), h2, N.lt_zero(n)))
    case 1n+g1 1n+g2:
      %Equal.sym(Nat & Nat, Nat.divmod(n, 10n), (RD.fst(Nat.divmod(n, 10n)), RD.snd(Nat.divmod(n, 10n))), RD.pair_eta(Nat.divmod(n, 10n))) :
        {Nat.show.fin(g1, acc, Nat.show.put(_)) == Nat.show.fin(g2, acc, Nat.show.put(_)) : String}
      fi.k(g1, g2, n, acc, Nat.div(n, 10n), {==},
        Equal.trans(Bool, Nat.is_le(n, g1), Nat.is_lt(n, 1n+g1), True{}, Equal.sym(Bool, Nat.is_lt(n, 1n+g1), Nat.is_le(n, g1), N.lt_succ_iff(n, g1)), h1),
        Equal.trans(Bool, Nat.is_le(n, g2), Nat.is_lt(n, 1n+g2), True{}, Equal.sym(Bool, Nat.is_lt(n, 1n+g2), Nat.is_le(n, g2), N.lt_succ_iff(n, g2)), h2),
        n2 => a2 => x1 => x2 => go_fuel(g1, g2, n2, a2, x1, x2))

def DCH(+r: Nat) -> String:
  SCon{Chr{U32.from_nat(Nat.add(48n, r))}, SNil{}}

# Nat.show(10q + r) is Nat.show(q) then r's digit (q >= 1).
def show_snoc(+q: Nat, +r: Nat, +hq: {Nat.is_le(1n, q) == True{} : Bool}, +hr: {Nat.is_lt(r, 10n) == True{} : Bool}) ->
  {Nat.show(Nat.add(Nat.mul(q, 10n), r)) == Nat.show(q) ++ DCH(r) : String}:
  match q:
    case 0n:
      Empty.absurd({Nat.show(Nat.add(Nat.mul(0n, 10n), r)) == Nat.show(0n) ++ DCH(r) : String}, N.false_ne_true(hq))
    case 1n+p:
      +m0 = Nat.add(Nat.mul(1n+p, 10n), r)
      +ch = {Chr{U32.from_nat(Nat.add(48n, r))} : Char}
      %Equal.sym(Nat & Nat, Nat.divmod(m0, 10n), (RD.fst(Nat.divmod(m0, 10n)), RD.snd(Nat.divmod(m0, 10n))), RD.pair_eta(Nat.divmod(m0, 10n))) :
        {Nat.show.fin(m0, SNil{}, Nat.show.put(_)) == Nat.show(1n+p) ++ DCH(r) : String}
      %Equal.sym(Nat, Nat.div(m0, 10n), 1n+p, N.div_mul_add(1n+p, 10n, r, hr)) :
        {Nat.show.fin(m0, SNil{}, (Chr{U32.from_nat(Nat.add(48n, Nat.mod(m0, 10n)))}, _)) == Nat.show(1n+p) ++ DCH(r) : String}
      %Equal.sym(Nat, Nat.mod(m0, 10n), r, N.mod_mul_add(1n+p, 10n, r, hr)) :
        {Nat.show.fin(m0, SNil{}, (Chr{U32.from_nat(Nat.add(48n, _))}, 1n+p)) == Nat.show(1n+p) ++ DCH(r) : String}
      %Equal.sym(String, Nat.show.go(m0, 1n+p, SCon{ch, SNil{}}), Nat.show.go(m0, 1n+p, "") ++ SCon{ch, SNil{}}, RD.go_acc(m0, 1n+p, SCon{ch, SNil{}})) :
        {_ == Nat.show(1n+p) ++ DCH(r) : String}
      %Equal.sym(String, Nat.show.go(m0, 1n+p, ""), Nat.show.go(1n+(1n+p), 1n+p, ""),
        go_fuel(m0, 1n+(1n+p), 1n+p, "", lt_m10(p, r), Equal.trans(Bool, Nat.is_lt(1n+p, 1n+(1n+p)), Nat.is_le(1n+p, 1n+p), True{}, N.lt_succ_iff(1n+p, 1n+p), N.le_refl(1n+p)))) :
        {_ ++ SCon{ch, SNil{}} == Nat.show(1n+p) ++ DCH(r) : String}
      {==}

def le_v10(+v: Nat, +dd: Nat) -> {Nat.is_le(v, Nat.add(Nat.mul(v, 10n), dd)) == True{} : Bool}:
  N.le_trans(v, Nat.mul(v, 10n), Nat.add(Nat.mul(v, 10n), dd), RD.le_mul10(v), N.le_add_r(Nat.mul(v, 10n), dd))

# The digit byte y is the character of its value.
def dig_chr(+y: U32, +hge: {U32.is_ge(y, 48) == True{} : Bool}) -> {U32.from_nat(Nat.add(48n, Nat.sub(U32.to_nat(y), 48n))) == y : U32}:
  Equal.trans(U32, U32.from_nat(Nat.add(48n, Nat.sub(U32.to_nat(y), 48n))), U32.from_nat(U32.to_nat(y)), y,
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.add(48n, Nat.sub(U32.to_nat(y), 48n)), U32.to_nat(y), N.le_sub_add(48n, U32.to_nat(y), Z.ule(48, y, LN.le48(y, hge)))),
    U.from_nat_to_nat(y))

def show_val(xs: List<&2, U32>, +v: Nat, +hv1: {Nat.is_le(1n, v) == True{} : Bool}, +hd: {alld(xs) == True{} : Bool}) ->
  {Nat.show(valn(xs, v)) == Nat.show(v) ++ Norm.chars(xs) : String}:
  match xs:
    case Nil{}:
      Equal.sym(String, Nat.show(v) ++ "", Nat.show(v), RB.s_append_nil(Nat.show(v)))
    case Con{+y, +t}:
      +dy = N.and_true_l(NF.is_digit(y), alld(t), hd)
      +hge = N.and_true_l(U32.is_ge(y, 48), U32.is_le(y, 57), dy)
      +hle = N.and_true_r(U32.is_ge(y, 48), U32.is_le(y, 57), dy)
      +dd = Nat.sub(U32.to_nat(y), 48n)
      +hd10 = Equal.trans(Bool, Nat.is_lt(dd, 10n), Nat.is_le(dd, 9n), True{}, N.lt_succ_iff(dd, 9n), LN.k9(y, hle))
      +v2 = Nat.add(Nat.mul(v, 10n), dd)
      +hv2 = N.le_trans(1n, v, v2, hv1, le_v10(v, dd))
      +ih = show_val(t, v2, hv2, N.and_true_r(NF.is_digit(y), alld(t), hd))
      +F = {Chr{U32.from_nat(Nat.add(48n, dd))} : Char}
      +S0 = Nat.show(v)
      +T0 = Norm.chars(t)
      Equal.trans(String, Nat.show(valn(t, v2)), Nat.show(v2) ++ T0, S0 ++ SCon{Chr{y}, T0}, ih,
        Equal.trans(String, Nat.show(v2) ++ T0, (S0 ++ DCH(dd)) ++ T0, S0 ++ SCon{Chr{y}, T0},
          Equal.cong(String, String, z => z ++ T0, Nat.show(v2), S0 ++ DCH(dd), show_snoc(v, dd, hv1, hd10)),
          Equal.trans(String, (S0 ++ DCH(dd)) ++ T0, S0 ++ SCon{F, T0}, S0 ++ SCon{Chr{y}, T0}, RB.s_append_assoc(S0, DCH(dd), T0),
            Equal.cong(U32, String, z => S0 ++ SCon{Chr{z}, T0}, U32.from_nat(Nat.add(48n, dd)), y, dig_chr(y, hge)))))

# A POS with no leading zero is written back as it is.
def show_head(+y: U32, +t: List<&2, U32>, +hd: {alld(Con{y, t}) == True{} : Bool}, +h48: {U32.is_eq(y, 48) == False{} : Bool}) ->
  {Nat.show(valn(Con{y, t}, 0n)) == Norm.chars(Con{y, t}) : String}:
  +dy = N.and_true_l(NF.is_digit(y), alld(t), hd)
  +hge = N.and_true_l(U32.is_ge(y, 48), U32.is_le(y, 57), dy)
  +hle = N.and_true_r(U32.is_ge(y, 48), U32.is_le(y, 57), dy)
  +dd = Nat.sub(U32.to_nat(y), 48n)
  +le48 = Z.ule(48, y, LN.le48(y, hge))
  +ne = Equal.trans(Bool, Nat.is_eq(48n, U32.to_nat(y)), Nat.is_eq(U32.to_nat(y), 48n), False{}, N.eq_comm(48n, U32.to_nat(y)),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(y), 48n), U32.is_eq(y, 48), False{}, Equal.sym(Bool, U32.is_eq(y, 48), Nat.is_eq(U32.to_nat(y), 48n), U.is_eq_to_nat(y, 48)), h48))
  +h1 = N.le_sub_r(48n, 1n, U32.to_nat(y), C.succ_le(48n, U32.to_nat(y), Z.le_ne_lt(48n, U32.to_nat(y), le48, ne)))
  +sv = show_val(t, dd, h1, N.and_true_r(NF.is_digit(y), alld(t), hd))
  Equal.trans(String, Nat.show(valn(t, dd)), Nat.show(dd) ++ Norm.chars(t), SCon{Chr{y}, Norm.chars(t)}, sv,
    Equal.trans(String, Nat.show(dd) ++ Norm.chars(t), DCH(dd) ++ Norm.chars(t), SCon{Chr{y}, Norm.chars(t)},
      Equal.cong(String, String, z => z ++ Norm.chars(t), Nat.show(dd), DCH(dd), show_small(dd, LN.k9(y, hle))),
      Equal.cong(U32, String, z => SCon{Chr{z}, Norm.chars(t)}, U32.from_nat(Nat.add(48n, dd)), y, dig_chr(y, hge))))

def valn_ge(xs: List<&2, U32>, +v: Nat) -> {Nat.is_le(v, valn(xs, v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      N.le_refl(v)
    case Con{+y, +t}:
      +v2 = Nat.add(Nat.mul(v, 10n), Nat.sub(U32.to_nat(y), 48n))
      N.le_trans(v, v2, valn(t, v2), le_v10(v, Nat.sub(U32.to_nat(y), 48n)), valn_ge(t, v2))

def ne0(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_eq(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, N.false_ne_true(h))
    case 1n+w:
      {==}

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(h))
    case False{}:
      {==}

def PLT(+L: List<&2, U32>, +v: Nat) -> Type:
  {B.Pos.read(Norm.chars(L)) == Some{v} : Maybe<&2, Nat>} & ({Nat.show(v) == Norm.chars(L) : String} & {Nat.is_eq(v, 0n) == False{} : Bool})

# Digits with no leading zero: read, written back, not zero.
def pos_list(+y: U32, +t: List<&2, U32>, +hd: {alld(Con{y, t}) == True{} : Bool}, +h48: {U32.is_eq(y, 48) == False{} : Bool}) ->
  PLT(Con{y, t}, valn(Con{y, t}, 0n)):
  +dy = N.and_true_l(NF.is_digit(y), alld(t), hd)
  +hge = N.and_true_l(U32.is_ge(y, 48), U32.is_le(y, 57), dy)
  +dd = Nat.sub(U32.to_nat(y), 48n)
  +le48 = Z.ule(48, y, LN.le48(y, hge))
  +ne = Equal.trans(Bool, Nat.is_eq(48n, U32.to_nat(y)), Nat.is_eq(U32.to_nat(y), 48n), False{}, N.eq_comm(48n, U32.to_nat(y)),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(y), 48n), U32.is_eq(y, 48), False{}, Equal.sym(Bool, U32.is_eq(y, 48), Nat.is_eq(U32.to_nat(y), 48n), U.is_eq_to_nat(y, 48)), h48))
  +h1 = N.le_sub_r(48n, 1n, U32.to_nat(y), C.succ_le(48n, U32.to_nat(y), Z.le_ne_lt(48n, U32.to_nat(y), le48, ne)))
  (pr_go(Con{y, t}, 0n, hd), (show_head(y, t, hd, h48), ne0(valn(t, dd), N.le_trans(1n, dd, valn(t, dd), h1, valn_ge(t, dd)))))

def pos_k(+kk: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hk1: {Nat.is_le(1n, kk) == True{} : Bool}, +hp: {Nat.is_le(Nat.add(Z.n(from), kk), Z.n(len)) == True{} : Bool},
  +hd: {alld(D.slice(Z.X(len, t), Z.n(from), kk)) == True{} : Bool}, +h48: {U32.is_eq(C.AT(len, t, from), 48) == False{} : Bool}) ->
  PLT(D.slice(Z.X(len, t), Z.n(from), kk), valn(D.slice(Z.X(len, t), Z.n(from), kk), 0n)):
  match kk:
    case 0n:
      Empty.absurd(PLT(D.slice(Z.X(len, t), Z.n(from), 0n), valn(D.slice(Z.X(len, t), Z.n(from), 0n), 0n)), N.false_ne_true(hk1))
    case 1n+k:
      +T = D.slice(Z.X(len, t), Z.n((from + 1 : U32)), k)
      %Equal.sym(List<&2, U32>, D.slice(Z.X(len, t), Z.n(from), 1n+k), C.AT(len, t, from) <> T, slc(len, t, d, from, k, hok, hp)) : PLT(_, valn(_, 0n))
      pos_list(C.AT(len, t, from), T, AB.subst(List<&2, U32>, z => {alld(z) == True{} : Bool}, D.slice(Z.X(len, t), Z.n(from), 1n+k), C.AT(len, t, from) <> T, slc(len, t, d, from, k, hok, hp), hd), h48)

def PCT(+len: U32, +t: AT.Tree<U32>, +a: Nat, +b: Nat, +pos: U32) -> Type:
  {B.Pos.read(S.fld(Z.X(len, t), a, b)) == Some{U32.to_nat(pos)} : Maybe<&2, Nat>} & ({Nat.show(U32.to_nat(pos)) == S.fld(Z.X(len, t), a, b) : String} & {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool})

def pos_fin(+kk: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +pos: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hk1: {Nat.is_le(1n, kk) == True{} : Bool}, +hp: {Nat.is_le(Nat.add(Z.n(from), kk), Z.n(len)) == True{} : Bool},
  +dig: {alld(D.slice(Z.X(len, t), Z.n(from), kk)) == True{} : Bool}, +h48: {U32.is_eq(C.AT(len, t, from), 48) == False{} : Bool},
  +hpos: {U32.to_nat(pos) == valn(D.slice(Z.X(len, t), Z.n(from), kk), 0n) : Nat}, +hk: {kk == Nat.sub(Z.n(to), Z.n(from)) : Nat}) ->
  PCT(len, t, Z.n(from), Z.n(to), pos):
  pl = pos_k(kk, len, t, d, from, hok, hk1, hp, dig, h48)
  pl2 = AB.subst(Nat, z => PLT(D.slice(Z.X(len, t), Z.n(from), kk), z), valn(D.slice(Z.X(len, t), Z.n(from), kk), 0n), U32.to_nat(pos), Equal.sym(Nat, U32.to_nat(pos), valn(D.slice(Z.X(len, t), Z.n(from), kk), 0n), hpos), pl)
  AB.subst(Nat, z => PLT(D.slice(Z.X(len, t), Z.n(from), z), U32.to_nat(pos)), kk, Nat.sub(Z.n(to), Z.n(from)), hk, pl2)

# POS from .. to-1, as num read it (M = 2^32, q = 429496729).
def pos_core(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +pos: U32, +M: Nat, +q: Nat,
  +hm: {Nat.pow(2n, 32n) == M : Nat}, +hcq: {U32.to_nat(429496729) == q : Nat}, +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hft: {Nat.is_le(Z.n(from), Z.n(to)) == True{} : Bool}, +htl: {Nat.is_le(Z.n(to), Z.n(len)) == True{} : Bool},
  +hnok: {M.Nv.ok(M.NUM(len, t, from, to)) == True{} : Bool}, +hnv: {M.Nv.v(M.NUM(len, t, from, to)) == pos : U32}) ->
  PCT(len, t, Z.n(from), Z.n(to), pos):
  +nn = (to - from : U32)
  +x0 = C.AT(len, t, from)
  +ok0 = nok0(len, t, from, to, hnok)
  +a1 = N.and_true_l(U32.is_le(1, nn) && U32.is_le(nn, 9), Bool.not(U32.is_eq(x0, 48)), ok0)
  +h48 = not_true(U32.is_eq(x0, 48), N.and_true_r(U32.is_le(1, nn) && U32.is_le(nn, 9), Bool.not(U32.is_eq(x0, 48)), ok0))
  +h1 = N.and_true_l(U32.is_le(1, nn), U32.is_le(nn, 9), a1)
  +h9 = N.and_true_r(U32.is_le(1, nn), U32.is_le(nn, 9), a1)
  +kk = U32.to_nat(nn)
  +hk = U.to_nat_sub_le(to, from, Z.nle(from, to, hft))
  +F = U32.to_nat(U32.min(nn, 10))
  +hf = fuel_eq(nn, h9)
  +ok1 = AB.subst(Nat, z => {M.Nv.ok(M.NG(z, len, t, x0, from, 0, NOK0(len, t, from, to))) == True{} : Bool}, F, kk, hf, hnok)
  +hp = AB.subst(Nat, z => {Nat.is_le(Nat.add(Z.n(from), z), Z.n(len)) == True{} : Bool}, Nat.sub(Z.n(to), Z.n(from)), kk, Equal.sym(Nat, kk, Nat.sub(Z.n(to), Z.n(from)), hk),
    AB.subst(Nat, z => {Nat.is_le(z, Z.n(len)) == True{} : Bool}, Z.n(to), Nat.add(Z.n(from), Nat.sub(Z.n(to), Z.n(from))), Equal.sym(Nat, Nat.add(Z.n(from), Nat.sub(Z.n(to), Z.n(from))), Z.n(to), N.le_sub_add(Z.n(from), Z.n(to), hft)), htl))
  +dig = ng_dig(kk, len, t, d, x0, from, 0, NOK0(len, t, from, to), hok, ok1, {==}, hp)
  +val = ng_v(kk, len, t, d, x0, from, 0, NOK0(len, t, from, to), 0n, M, q, hm, hcq, hq, hok, ok1, {==}, hp, Z.ule(nn, 9, h9), {==}, 0n, {==})
  +hpos = Equal.trans(Nat, U32.to_nat(pos), U32.to_nat(M.Nv.v(M.NG(kk, len, t, x0, from, 0, NOK0(len, t, from, to)))), valn(D.slice(Z.X(len, t), Z.n(from), kk), 0n),
    Equal.trans(Nat, U32.to_nat(pos), U32.to_nat(M.Nv.v(M.NUM(len, t, from, to))), U32.to_nat(M.Nv.v(M.NG(kk, len, t, x0, from, 0, NOK0(len, t, from, to)))),
      Equal.cong(U32, Nat, z => U32.to_nat(z), pos, M.Nv.v(M.NUM(len, t, from, to)), Equal.sym(U32, M.Nv.v(M.NUM(len, t, from, to)), pos, hnv)),
      Equal.cong(Nat, Nat, z => U32.to_nat(M.Nv.v(M.NG(z, len, t, x0, from, 0, NOK0(len, t, from, to)))), F, kk, hf)),
    val)
  pos_fin(kk, len, t, d, from, to, pos, hok, Z.ule(1, nn, h1), hp, dig, h48, hpos, hk)

# ---------------------------------------------------------------------------
# POS is below 10^9: after K <= 9 digits num's value is at most PK(K)
# ---------------------------------------------------------------------------

def pk_lt9(+K: Nat, +h: {Nat.is_le(K, 9n) == True{} : Bool}) -> {U32.is_lt(PK(K), 1000000000) == True{} : Bool}:
  match K:
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
      Empty.absurd({U32.is_lt(PK(10n+k), 1000000000) == True{} : Bool}, N.false_ne_true(h))

def ng_b(+m: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +j: U32, +acc: U32, +ok: Bool, +J: Nat, +K: Nat, +M: Nat, +q: Nat,
  +hm: {Nat.pow(2n, 32n) == M : Nat}, +hcq: {U32.to_nat(429496729) == q : Nat}, +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat},
  +h: {M.Nv.ok(M.NG(m, len, t, x, j, acc, ok)) == True{} : Bool}, +hJK: {Nat.add(J, m) == K : Nat}, +hK: {Nat.is_le(K, 9n) == True{} : Bool},
  +hacc: {U32.is_le(acc, PK(J)) == True{} : Bool}) -> {U32.is_le(M.Nv.v(M.NG(m, len, t, x, j, acc, ok)), PK(K)) == True{} : Bool}:
  match m:
    case 0n:
      AB.subst(Nat, z => {U32.is_le(acc, PK(z)) == True{} : Bool}, J, K, Equal.trans(Nat, J, Nat.add(J, 0n), K, Equal.sym(Nat, Nat.add(J, 0n), J, N.add_zero(J)), hJK), hacc)
    case 1n+k:
      +dx = ng_dx(k, len, t, x, j, acc, ok, h)
      +hge = N.and_true_l(U32.is_ge(x, 48), U32.is_le(x, 57), dx)
      +hle = N.and_true_r(U32.is_ge(x, 48), U32.is_le(x, 57), dx)
      +hJK2 = Equal.trans(Nat, 1n+Nat.add(J, k), Nat.add(J, 1n+k), K, Equal.sym(Nat, Nat.add(J, 1n+k), 1n+Nat.add(J, k), N.add_succ(J, k)), hJK)
      +hJs = AB.subst(Nat, z => {Nat.is_le(z, 9n) == True{} : Bool}, K, 1n+Nat.add(J, k), Equal.sym(Nat, 1n+Nat.add(J, k), K, hJK2), hK)
      +hJ8 = N.le_trans(J, Nat.add(J, k), 8n, N.le_add_r(J, k), hJs)
      ng_b(k, len, t, C.AT(len, t, (j + 1 : U32)), (j + 1 : U32), LN.NA(acc, x), ok && NF.is_digit(x), 1n+J, K, M, q, hm, hcq, hq, h, hJK2, hK,
        stp_b1(acc, x, J, M, q, hm, hcq, hq, hJ8, hacc, hge, hle))

def pos_small(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +pos: U32, +M: Nat, +q: Nat,
  +hm: {Nat.pow(2n, 32n) == M : Nat}, +hcq: {U32.to_nat(429496729) == q : Nat}, +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat},
  +hnok: {M.Nv.ok(M.NUM(len, t, from, to)) == True{} : Bool}, +hnv: {M.Nv.v(M.NUM(len, t, from, to)) == pos : U32}) ->
  {U32.is_lt(pos, 1000000000) == True{} : Bool}:
  +nn = (to - from : U32)
  +x0 = C.AT(len, t, from)
  +ok0 = nok0(len, t, from, to, hnok)
  +a1 = N.and_true_l(U32.is_le(1, nn) && U32.is_le(nn, 9), Bool.not(U32.is_eq(x0, 48)), ok0)
  +h9 = N.and_true_r(U32.is_le(1, nn), U32.is_le(nn, 9), a1)
  +kk = U32.to_nat(nn)
  +F = U32.to_nat(U32.min(nn, 10))
  +hf = fuel_eq(nn, h9)
  +ok1 = AB.subst(Nat, z => {M.Nv.ok(M.NG(z, len, t, x0, from, 0, NOK0(len, t, from, to))) == True{} : Bool}, F, kk, hf, hnok)
  +hk9 = Z.ule(nn, 9, h9)
  +b = ng_b(kk, len, t, x0, from, 0, NOK0(len, t, from, to), 0n, kk, M, q, hm, hcq, hq, ok1, {==}, hk9, {==})
  +lt = u_le_lt(M.Nv.v(M.NG(kk, len, t, x0, from, 0, NOK0(len, t, from, to))), PK(kk), 1000000000, b, pk_lt9(kk, hk9))
  +lt2 = AB.subst(Nat, z => {U32.is_lt(M.Nv.v(M.NG(z, len, t, x0, from, 0, NOK0(len, t, from, to))), 1000000000) == True{} : Bool}, kk, F, Equal.sym(Nat, F, kk, hf), lt)
  AB.subst(U32, z => {U32.is_lt(z, 1000000000) == True{} : Bool}, M.Nv.v(M.NUM(len, t, from, to)), pos, hnv, lt2)
