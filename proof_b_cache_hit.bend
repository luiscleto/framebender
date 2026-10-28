import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./norm_fast.bend as NF
import ./proof_b_cachedefs.bend as CD
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_same.bend as SM
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ./proof_b_lit.bend as LT
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./norm_run.bend as NR
import ./proof_b_defs.bend as PD
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_num.bend as NM
import ./proof_b_run_sz.bend as SZ
import ./proof_b_run_buf.bend as BF
import ./proof_b_cache_lem.bend as X
import ../lawful-bytes/proof_grow.bend as G
import ../lawful-bytes/proof_seq.bend as Q
import ../lawful-bytes/proof_list.bend as PLS
import ../lawful-bytes/proof_ops.bend as O

# The fast path's REF test (NF.refeq) for proof_b_cache.bend's against_hit:
# the loop hands both buffers back; a passed test means each REF byte equals
# the window's letter up to case; with REF upper-case ACGTN, the bases agree.

# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------

# Two bytes equal up to case (refeq's test).
def zq(+x: U32, +y: U32) -> Bool:
  U32.is_zero(((x .^. y : U32) .&. 223 : U32))

# The loop's value, on mirrors.
def RQG(m: Nat, +l1: U32, +t1: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +i: U32, +j: U32, acc: Bool) -> Bool:
  match m:
    case 0n:
      acc
    case 1n+k:
      RQG(k, l1, t1, l2, t2, (i + 1 : U32), (j + 1 : U32), acc && zq(C.AT(l1, t1, i), C.AT(l2, t2, j)))

def rq_pair(+m: Nat, +l1: U32, +t1: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +i: U32, +j: U32, +acc: Bool) ->
  {NF.refeq.k(m, i, j, acc, BY.at(C.BT(l1, t1), i), BY.at(C.BT(l2, t2), j)) == (C.BT(l1, t1), (C.BT(l2, t2), RQG(m, l1, t1, l2, t2, i, j, acc))) : D.Bytes & (D.Bytes & Bool)}:
  match m:
    case 0n:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(l1, t1), i), (C.BT(l1, t1), C.AT(l1, t1, i)), C.at_pair_t(l1, t1, i)) :
        {NF.refeq.k(0n, i, j, acc, _, BY.at(C.BT(l2, t2), j)) == (C.BT(l1, t1), (C.BT(l2, t2), RQG(0n, l1, t1, l2, t2, i, j, acc))) : D.Bytes & (D.Bytes & Bool)}
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(l2, t2), j), (C.BT(l2, t2), C.AT(l2, t2, j)), C.at_pair_t(l2, t2, j)) :
        {NF.refeq.k(0n, i, j, acc, (C.BT(l1, t1), C.AT(l1, t1, i)), _) == (C.BT(l1, t1), (C.BT(l2, t2), RQG(0n, l1, t1, l2, t2, i, j, acc))) : D.Bytes & (D.Bytes & Bool)}
      {==}
    case 1n+k:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(l1, t1), i), (C.BT(l1, t1), C.AT(l1, t1, i)), C.at_pair_t(l1, t1, i)) :
        {NF.refeq.k(1n+k, i, j, acc, _, BY.at(C.BT(l2, t2), j)) == (C.BT(l1, t1), (C.BT(l2, t2), RQG(1n+k, l1, t1, l2, t2, i, j, acc))) : D.Bytes & (D.Bytes & Bool)}
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(l2, t2), j), (C.BT(l2, t2), C.AT(l2, t2, j)), C.at_pair_t(l2, t2, j)) :
        {NF.refeq.k(1n+k, i, j, acc, (C.BT(l1, t1), C.AT(l1, t1, i)), _) == (C.BT(l1, t1), (C.BT(l2, t2), RQG(1n+k, l1, t1, l2, t2, i, j, acc))) : D.Bytes & (D.Bytes & Bool)}
      rq_pair(k, l1, t1, l2, t2, (i + 1 : U32), (j + 1 : U32), acc && zq(C.AT(l1, t1, i), C.AT(l2, t2, j)))

def rq_acc(+m: Nat, +l1: U32, +t1: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +i: U32, +j: U32, +acc: Bool,
  +h: {RQG(m, l1, t1, l2, t2, i, j, acc) == True{} : Bool}) -> {acc == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+k:
      +z = zq(C.AT(l1, t1, i), C.AT(l2, t2, j))
      N.and_true_l(acc, z, rq_acc(k, l1, t1, l2, t2, (i + 1 : U32), (j + 1 : U32), acc && z, h))

# Pairs equal up to case, one by one.
def rql(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Con{+x, xt} Con{+y, yt}:
      zq(x, y) && rql(xt, yt)
    case _ _:
      True{}

def take0l(+xs: List<&2, U32>) -> {List.take(&2, U32, xs, 0n) == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# A passed test: the slices are equal up to case.
def rq_val(+m: Nat, +l1: U32, +t1: AT.Tree<U32>, +d1: Nat, +l2: U32, +t2: AT.Tree<U32>, +d2: Nat, +i: U32, +j: U32, +acc: Bool,
  +h1: {D.ok(C.BT(l1, t1), d1) == True{} : Bool},
  +h2: {D.ok(C.BT(l2, t2), d2) == True{} : Bool},
  +hi: {Nat.is_le(Nat.add(U32.to_nat(i), m), U32.to_nat(l1)) == True{} : Bool},
  +hj: {Nat.is_le(Nat.add(U32.to_nat(j), m), U32.to_nat(l2)) == True{} : Bool},
  +h: {RQG(m, l1, t1, l2, t2, i, j, acc) == True{} : Bool}) ->
  {rql(D.slice(D.view(C.BT(l1, t1)), U32.to_nat(i), m), D.slice(D.view(C.BT(l2, t2)), U32.to_nat(j), m)) == True{} : Bool}:
  match m:
    case 0n:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, D.view(C.BT(l1, t1)), U32.to_nat(i)), 0n), Nil{}, take0l(List.drop(&2, U32, D.view(C.BT(l1, t1)), U32.to_nat(i)))) :
        {rql(_, D.slice(D.view(C.BT(l2, t2)), U32.to_nat(j), 0n)) == True{} : Bool}
      {==}
    case 1n+k:
      +x = C.AT(l1, t1, i)
      +y = C.AT(l2, t2, j)
      +v1 = D.view(C.BT(l1, t1))
      +v2 = D.view(C.BT(l2, t2))
      +ih = rq_val(k, l1, t1, d1, l2, t2, d2, (i + 1 : U32), (j + 1 : U32), acc && zq(x, y), h1, h2, SM.step_le(l1, t1, d1, i, k, h1, hi), SM.step_le(l2, t2, d2, j, k, h2, hj), h)
      +hz = N.and_true_r(acc, zq(x, y), rq_acc(k, l1, t1, l2, t2, (i + 1 : U32), (j + 1 : U32), acc && zq(x, y), h))
      %Equal.sym(List<&2, U32>, D.slice(v1, U32.to_nat(i), 1n+k), x <> D.slice(v1, Nat.add(U32.to_nat(i), 1n), k), SM.slice_cons(v1, U32.to_nat(i), k, x, SM.step_val(l1, t1, d1, i, k, h1, hi))) : {rql(_, D.slice(v2, U32.to_nat(j), 1n+k)) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.slice(v2, U32.to_nat(j), 1n+k), y <> D.slice(v2, Nat.add(U32.to_nat(j), 1n), k), SM.slice_cons(v2, U32.to_nat(j), k, y, SM.step_val(l2, t2, d2, j, k, h2, hj))) : {rql(x <> D.slice(v1, Nat.add(U32.to_nat(i), 1n), k), _) == True{} : Bool}
      %Equal.sym(Bool, zq(x, y), True{}, hz) : {Bool.and(_, rql(D.slice(v1, Nat.add(U32.to_nat(i), 1n), k), D.slice(v2, Nat.add(U32.to_nat(j), 1n), k))) == True{} : Bool}
      %SM.step_inc(l1, t1, d1, i, k, h1, hi) : {rql(D.slice(v1, _, k), D.slice(v2, Nat.add(U32.to_nat(j), 1n), k)) == True{} : Bool}
      %SM.step_inc(l2, t2, d2, j, k, h2, hj) : {rql(D.slice(v1, U32.to_nat((i + 1 : U32)), k), D.slice(v2, _, k)) == True{} : Bool}
      ih

# ---------------------------------------------------------------------------
# One byte: an upper-case base and a letter equal up to case
# ---------------------------------------------------------------------------

# Not equal up to case, or the letter reads as the base.
def okb(+x: U32, +y: U32) -> Bool:
  Bool.or(Bool.not(zq(x, y)), B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)))

# okb for every byte below k (checked by computation for k = 256).
def chk(k: Nat, +x: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+(+p):
      okb(x, U32.from_nat(p)) && chk(p, x)

def chk.k(+q: Nat, +x: U32, +p: Nat, +e: Bool, +he: {Nat.is_eq(p, q) == e : Bool},
  +h: {Bool.and(okb(x, U32.from_nat(q)), chk(q, x)) == True{} : Bool},
  +hp: {Nat.is_lt(p, 1n+q) == True{} : Bool},
  ih: {Nat.is_lt(p, q) == True{} : Bool} -> {okb(x, U32.from_nat(p)) == True{} : Bool}) ->
  {okb(x, U32.from_nat(p)) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, p, q, N.eq_sound(p, q, he)) : {okb(x, U32.from_nat(_)) == True{} : Bool}
      N.and_true_l(okb(x, U32.from_nat(q)), chk(q, x), h)
    case False{}:
      +hle = Equal.trans(Bool, Nat.is_le(p, q), Nat.is_lt(p, 1n+q), True{}, Equal.sym(Bool, Nat.is_lt(p, 1n+q), Nat.is_le(p, q), N.lt_succ_iff(p, q)), hp)
      ih(Equal.trans(Bool, Nat.is_lt(p, q), Nat.is_le(1n+p, q), True{}, Equal.sym(Bool, Nat.is_le(1n+p, q), Nat.is_lt(p, q), N.le_succ_lt(p, q)), N.le_ne(p, q, hle, he)))

def chk_ok(+k: Nat, +x: U32, +h: {chk(k, x) == True{} : Bool}, +p: Nat, +hp: {Nat.is_lt(p, k) == True{} : Bool}) ->
  {okb(x, U32.from_nat(p)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({okb(x, U32.from_nat(p)) == True{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, N.lt_zero(p)), hp)))
    case 1n+q:
      chk.k(q, x, p, Nat.is_eq(p, q), {==}, h, hp, hl => chk_ok(q, x, N.and_true_r(okb(x, U32.from_nat(q)), chk(q, x), h), p, hl))

# A byte below 256 against base x (any x for which chk(256) holds).
def okb_y(+x: U32, +y: U32, +hc: {chk(256n, x) == True{} : Bool}, +hy: {U32.is_lt(y, 256) == True{} : Bool}) ->
  {okb(x, y) == True{} : Bool}:
  +hp = Equal.trans(Bool, Nat.is_lt(U32.to_nat(y), 256n), U32.is_lt(y, 256), True{}, Equal.sym(Bool, U32.is_lt(y, 256), Nat.is_lt(U32.to_nat(y), 256n), U.is_lt_to_nat(y, 256)), hy)
  AB.subst(U32, z => {okb(x, z) == True{} : Bool}, U32.from_nat(U32.to_nat(y)), y, U.from_nat_to_nat(y), chk_ok(256n, x, hc, U32.to_nat(y), hp))

def okb_eq(+x: U32, +y: U32, +h: {okb(x, y) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  AB.subst(Bool, z => {Bool.or(Bool.not(z), B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x))) == True{} : Bool}, zq(x, y), True{}, hz, h)

def pb.w(+x: U32, +w: U32, +y: U32, +hw: {x == w : U32}, +hc: {chk(256n, w) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  %Equal.sym(U32, x, w, hw) : {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(_)) == True{} : Bool}
  okb_eq(w, y, okb_y(w, y, hc, hy), AB.subst(U32, z => {zq(z, y) == True{} : Bool}, x, w, hw, hz))

def pb5(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 78) == e : Bool}, +h: {e == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 78, y, U.is_eq_true(x, 78, he), {==}, hy, hz)
    case False{}:
      Empty.absurd({B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}, N.false_ne_true(h))

def pb4(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 84) == e : Bool}, +h: {Bool.or(e, U32.is_eq(x, 78)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 84, y, U.is_eq_true(x, 84, he), {==}, hy, hz)
    case False{}:
      pb5(x, y, U32.is_eq(x, 78), {==}, h, hy, hz)

def pb3(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 71) == e : Bool}, +h: {Bool.or(Bool.or(e, U32.is_eq(x, 84)), U32.is_eq(x, 78)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 71, y, U.is_eq_true(x, 71, he), {==}, hy, hz)
    case False{}:
      pb4(x, y, U32.is_eq(x, 84), {==}, h, hy, hz)

def pb2(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 67) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 71)), U32.is_eq(x, 84)), U32.is_eq(x, 78)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 67, y, U.is_eq_true(x, 67, he), {==}, hy, hz)
    case False{}:
      pb3(x, y, U32.is_eq(x, 71), {==}, h, hy, hz)

def pb1(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 65) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 67)), U32.is_eq(x, 71)), U32.is_eq(x, 84)), U32.is_eq(x, 78)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 65, y, U.is_eq_true(x, 65, he), {==}, hy, hz)
    case False{}:
      pb2(x, y, U32.is_eq(x, 67), {==}, h, hy, hz)

# An upper-case base byte and a byte equal to it up to case: the same base.
def pb(+x: U32, +y: U32, +hx: {NF.is_base(x) == True{} : Bool}, +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)) == True{} : Bool}:
  pb1(x, y, U32.is_eq(x, 65), {==}, hx, hy, hz)

# REF bytes (upper-case bases) equal up to case to letter bytes: their bases
# are the letters' bases.
def bq(+xs: List<&2, U32>, +ys: List<&2, U32>,
  +hr: {rql(xs, ys) == True{} : Bool},
  +hu: {CD.up(xs) == True{} : Bool},
  +hb: {D.all_bytes(ys) == True{} : Bool},
  +hl: {List.length(&2, U32, xs) == List.length(&2, U32, ys) : Nat}) ->
  {B.Bases.eq(B.Bases.of_fasta(Norm.chars(ys)), CD.bases_of(xs)) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({B.Bases.eq(B.Bases.of_fasta(Norm.chars(Con{y, yt})), CD.bases_of(Nil{})) == True{} : Bool}, N.zero_ne_succ(List.length(&2, U32, yt), hl))
    case Con{x, xt} Nil{}:
      Empty.absurd({B.Bases.eq(B.Bases.of_fasta(Norm.chars(Nil{})), CD.bases_of(Con{x, xt})) == True{} : Bool}, N.succ_ne_zero(List.length(&2, U32, xt), hl))
    case Con{x, xt} Con{y, yt}:
      +hz = N.and_true_l(zq(x, y), rql(xt, yt), hr)
      +hx = N.and_true_l(NF.is_base(x), CD.up(xt), hu)
      +hy = N.and_true_l(U32.is_lt(y, 256), D.all_bytes(yt), hb)
      %Equal.sym(Bool, B.Base.is_eq(B.Base.of_fasta(Chr{y}), CD.lb(x)), True{}, pb(x, y, hx, hy, hz)) :
        {Bool.and(_, B.Bases.eq(B.Bases.of_fasta(Norm.chars(yt)), CD.bases_of(xt))) == True{} : Bool}
      bq(xt, yt, N.and_true_r(zq(x, y), rql(xt, yt), hr), N.and_true_r(NF.is_base(x), CD.up(xt), hu), N.and_true_r(U32.is_lt(y, 256), D.all_bytes(yt), hb), N.succ_inj(List.length(&2, U32, xt), List.length(&2, U32, yt), hl))

# ---------------------------------------------------------------------------
# Word facts (powers stay symbolic; the word 2^31 only through LT.lit31w)
# ---------------------------------------------------------------------------

def P31() -> Nat:
  Nat.pow(2n, 31n)

# fits31(n): the word reads back as n, and n < 2^31.
def f31_eq(+n: Nat, +h: {Norm.fits31(n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(n)) == n : Nat}:
  N.eq_sound(U32.to_nat(U32.from_nat(n)), n, N.and_true_l(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), U32.is_lt(U32.from_nat(n), 2147483648), h))

def f31_lt(+n: Nat, +h: {Norm.fits31(n) == True{} : Bool}) -> {Nat.is_lt(n, Nat.pow(2n, 31n)) == True{} : Bool}:
  +hw = N.and_true_r(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), U32.is_lt(U32.from_nat(n), 2147483648), h)
  +h1 = Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.from_nat(n)), U32.to_nat(2147483648)), U32.is_lt(U32.from_nat(n), 2147483648), True{}, Equal.sym(Bool, U32.is_lt(U32.from_nat(n), 2147483648), Nat.is_lt(U32.to_nat(U32.from_nat(n)), U32.to_nat(2147483648)), U.is_lt_to_nat(U32.from_nat(n), 2147483648)), hw)
  +h2 = AB.subst(Nat, z => {Nat.is_lt(z, U32.to_nat(2147483648)) == True{} : Bool}, U32.to_nat(U32.from_nat(n)), n, f31_eq(n, h), h1)
  AB.subst(Nat, z => {Nat.is_lt(n, z) == True{} : Bool}, U32.to_nat(2147483648), Nat.pow(2n, 31n), LT.lit31w(), h2)

# 4 * 2^d <= 2^e for 2 + d <= e (e kept a variable: the checker would
# expand a closed power it compares after unfolding).
def four_pow.g(+d: Nat, +e: Nat, +h: {Nat.is_le(Nat.add(2n, d), e) == True{} : Bool}) -> {Nat.is_le(Nat.mul(4n, Nat.pow(2n, d)), Nat.pow(2n, e)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(z, Nat.pow(2n, e)) == True{} : Bool}, Nat.pow(2n, Nat.add(2n, d)), Nat.mul(Nat.pow(2n, 2n), Nat.pow(2n, d)), N.pow_add(2n, 2n, d),
    N.pow_le(Nat.add(2n, d), e, h))

# 4 * 2^d <= 2^31 for d <= 29.
def four_pow(+d: Nat, +hd: {Nat.is_le(d, 29n) == True{} : Bool}) -> {Nat.is_le(Nat.mul(4n, Nat.pow(2n, d)), Nat.pow(2n, 31n)) == True{} : Bool}:
  four_pow.g(d, 31n, hd)

# x < 2^31 and y <= 2^31: x + y < 2^32.
def sum32(+x: Nat, +y: Nat, +hx: {Nat.is_lt(x, Nat.pow(2n, 31n)) == True{} : Bool}, +hy: {Nat.is_le(y, Nat.pow(2n, 31n)) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(x, y), Nat.pow(2n, 32n)) == True{} : Bool}:
  +P = Nat.pow(2n, 31n)
  +h1 = N.lt_le_trans(Nat.add(x, y), Nat.add(P, y), Nat.add(P, P), N.lt_add_mono_r(y, x, P, hx), N.le_add_mono_l(P, y, P, hy))
  +e = Equal.trans(Nat, Nat.add(P, P), Nat.double(P), Nat.pow(2n, 1n+31n), Equal.sym(Nat, Nat.double(P), Nat.add(P, P), N.dbl_add(P)), Equal.sym(Nat, Nat.pow(2n, 1n+31n), Nat.double(P), N.pow2s(31n)))
  AB.subst(Nat, z => {Nat.is_lt(Nat.add(x, y), z) == True{} : Bool}, Nat.add(P, P), Nat.pow(2n, 32n), e, h1)

# A word below the word 10^9 reads below 2^31.
def pos31(+w: U32, +h: {U32.is_lt(w, 1000000000) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(w), Nat.pow(2n, 31n)) == True{} : Bool}:
  +h1 = Equal.trans(Bool, Nat.is_lt(U32.to_nat(w), U32.to_nat(1000000000)), U32.is_lt(w, 1000000000), True{}, Equal.sym(Bool, U32.is_lt(w, 1000000000), Nat.is_lt(U32.to_nat(w), U32.to_nat(1000000000)), U.is_lt_to_nat(w, 1000000000)), h)
  +h2 = Equal.trans(Bool, Nat.is_lt(U32.to_nat(1000000000), U32.to_nat(2147483648)), U32.is_lt(1000000000, 2147483648), True{}, Equal.sym(Bool, U32.is_lt(1000000000, 2147483648), Nat.is_lt(U32.to_nat(1000000000), U32.to_nat(2147483648)), U.is_lt_to_nat(1000000000, 2147483648)), {==})
  AB.subst(Nat, z => {Nat.is_lt(U32.to_nat(w), z) == True{} : Bool}, U32.to_nat(2147483648), Nat.pow(2n, 31n), LT.lit31w(),
    N.lt_trans(U32.to_nat(w), U32.to_nat(1000000000), U32.to_nat(2147483648), h1, h2))

# ---------------------------------------------------------------------------
# Lists and Nats
# ---------------------------------------------------------------------------

def take_len_n(+ys: List<&2, U32>, +n: Nat, +h: {Nat.is_le(n, List.length(&2, U32, ys)) == True{} : Bool}) ->
  {List.length(&2, U32, List.take(&2, U32, ys, n)) == n : Nat}:
  match ys n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      Empty.absurd({List.length(&2, U32, List.take(&2, U32, Nil{}, 1n+k)) == 1n+k : Nat}, N.false_ne_true(h))
    case Con{y, t} 0n:
      {==}
    case Con{y, t} 1n+k:
      %take_len_n(t, k, h) : {1n+List.length(&2, U32, List.take(&2, U32, t, k)) == 1n+_ : Nat}
      {==}

# A slice within the list has n elements.
def sl_len(+xs: List<&2, U32>, +i: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(i, n), List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.length(&2, U32, D.slice(xs, i, n)) == n : Nat}:
  match xs i:
    case _ 0n:
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, xs, 0n), xs, X.drop0(xs)) : {List.length(&2, U32, List.take(&2, U32, _, n)) == n : Nat}
      take_len_n(xs, n, h)
    case Nil{} 1n+j:
      Empty.absurd({List.length(&2, U32, D.slice(Nil{}, 1n+j, n)) == n : Nat}, N.false_ne_true(h))
    case Con{x, t} 1n+j:
      sl_len(t, j, n, h)

def ab_drop(+xs: List<&2, U32>, +i: Nat, +h: {D.all_bytes(xs) == True{} : Bool}) -> {D.all_bytes(List.drop(&2, U32, xs, i)) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      h
    case Con{x, t} 1n+j:
      ab_drop(t, j, N.and_true_r(U32.is_lt(x, 256), D.all_bytes(t), h))

def ab_slice(+xs: List<&2, U32>, +i: Nat, +n: Nat, +h: {D.all_bytes(xs) == True{} : Bool}) -> {D.all_bytes(D.slice(xs, i, n)) == True{} : Bool}:
  Q.all_bytes_take(List.drop(&2, U32, xs, i), n, ab_drop(xs, i, h))

def len_bases_of(+xs: List<&2, U32>) -> {List.length(&2, B.Base, CD.bases_of(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %len_bases_of(t) : {1n+List.length(&2, B.Base, CD.bases_of(t)) == 1n+_ : Nat}
      {==}

# x + n <= o + l and o <= x: (x - o) + n <= l.
def sub_lin(+x: Nat, +o: Nat, +n: Nat, +l: Nat, +h1: {Nat.is_le(Nat.add(x, n), Nat.add(o, l)) == True{} : Bool}, +h2: {Nat.is_le(o, x) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.sub(x, o), n), l) == True{} : Bool}:
  match x o:
    case _ 0n:
      %N.sub_zero(x) : {Nat.is_le(Nat.add(_, n), l) == True{} : Bool}
      h1
    case 0n 1n+p:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(0n, 1n+p), n), l) == True{} : Bool}, N.false_ne_true(h2))
    case 1n+q 1n+p:
      sub_lin(q, p, n, l, h1, h2)

def min_le_r(+b: Nat, +l: Nat) -> {Nat.is_le(Nat.min(b, l), l) == True{} : Bool}:
  match b l:
    case 0n _:
      N.le_zero_l(l)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_r(p, q)

# x < w as words: x <= w.
def u_le_of_lt(+x: U32, +w: U32, +h: {U32.is_lt(x, w) == True{} : Bool}) -> {U32.is_le(x, w) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_le(x, w), Nat.is_le(U32.to_nat(x), U32.to_nat(w)), U.is_le_to_nat(x, w)) : {_ == True{} : Bool}
  N.lt_to_le(U32.to_nat(x), U32.to_nat(w), Equal.trans(Bool, Nat.is_lt(U32.to_nat(x), U32.to_nat(w)), U32.is_lt(x, w), True{}, Equal.sym(Bool, U32.is_lt(x, w), Nat.is_lt(U32.to_nat(x), U32.to_nat(w)), U.is_lt_to_nat(x, w)), h))

def fits_le31(+n: Nat, +h: {Norm.fits31(n) == True{} : Bool}) -> {Norm.le31(n) == True{} : Bool}:
  +hw = N.and_true_r(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), U32.is_lt(U32.from_nat(n), 2147483648), h)
  %Equal.sym(Bool, Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), True{}, N.and_true_l(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), U32.is_lt(U32.from_nat(n), 2147483648), h)) :
    {Bool.and(_, U32.is_le(U32.from_nat(n), 2147483648)) == True{} : Bool}
  u_le_of_lt(U32.from_nat(n), 2147483648, hw)

def ofs(+s: String,
  hb: {E.is_bytes(s) == True{} : Bool},
  hn: {Norm.len_le(s, 268435456) == True{} : Bool}) ->
  &l: U32 -> &t: AT.Tree<U32> -> &d: Nat ->
  ({NR.of_str(s) == C.BT(l, t) : D.Bytes}
  & ({D.ok(C.BT(l, t), d) == True{} : Bool}
  & {NR.chars(D.view(C.BT(l, t))) == s : String})):
  +L = String.length(s)
  +t0 = G.tnew(0n, 0)
  +h30 = N.le_trans(L, Nat.pow(2n, 28n), Nat.pow(2n, 30n), SZ.len28(s, hn), N.pow_le(28n, 30n, {==}))
  +hL = NM.lt_c0(L, Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(L, h30))
  +hok0 = AB.subst(D.Bytes, z => {D.ok(z, 0n) == True{} : Bool}, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n), G.empty_ok(0n, {==}))
  +eq = AB.subst(D.Bytes, z => {NR.put_str(z, s) == C.BT(BF.pstl(s, 0), BF.PSR(0, t0, s)) : D.Bytes}, C.BT(0, t0), BY.empty(0n),
    Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n)), BF.put_str_eq(0, t0, s, G.tnew_full(0n, 0)))
  (BF.pstl(s, 0), (BF.PSR(0, t0, s), (RD.tdepth(BF.PSR(0, t0, s)),
    (eq,
    (BF.put_str_ok(0, t0, 0n, s, hok0, hL),
    BF.put_str_text(0, t0, 0n, s, hok0, hb, hL))))))

# ---------------------------------------------------------------------------
# The CHROM test passed: CHROM's text is the window's contig
# ---------------------------------------------------------------------------

def f2(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +c: String, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool}) ->
  {PD.btext(bl, bt, s, (e0 - s : U32)) == c : String}:
  +n = (e0 - s : U32)
  +SLb = D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(n))
  +SLc = D.slice(D.view(C.BT(cbl, cbt)), U32.to_nat(0), U32.to_nat(n))
  +en = U.is_eq_true(n, cbl, hz)
  +hsU = Equal.trans(Bool, U32.is_le(s, e0), Nat.is_le(U32.to_nat(s), U32.to_nat(e0)), True{}, U.is_le_to_nat(s, e0), hs)
  +enat = U.to_nat_sub_le(e0, s, hsU)
  +hi1 = AB.subst(Nat, w => {Nat.is_le(Nat.add(U32.to_nat(s), w), U32.to_nat(bl)) == True{} : Bool}, Nat.sub(U32.to_nat(e0), U32.to_nat(s)), U32.to_nat(n), Equal.sym(Nat, U32.to_nat(n), Nat.sub(U32.to_nat(e0), U32.to_nat(s)), enat),
    AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(bl)) == True{} : Bool}, U32.to_nat(e0), Nat.add(U32.to_nat(s), Nat.sub(U32.to_nat(e0), U32.to_nat(s))),
      Equal.sym(Nat, Nat.add(U32.to_nat(s), Nat.sub(U32.to_nat(e0), U32.to_nat(s))), U32.to_nat(e0), N.le_sub_add(U32.to_nat(s), U32.to_nat(e0), hs)), he))
  +hj1 = AB.subst(U32, w => {Nat.is_le(Nat.add(U32.to_nat(0), U32.to_nat(w)), U32.to_nat(cbl)) == True{} : Bool}, cbl, n, Equal.sym(U32, n, cbl, en), N.le_refl(U32.to_nat(cbl)))
  +V = Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, n)))
  +hvl = SM.same_view_t(bl, bt, cbl, cbt, bd, cbd, s, 0, n, hok, okcb, hi1, hj1)
  +e1 = PLS.list_eq_true(SLb, SLc, Equal.trans(Bool, D.list_eq(SLb, SLc), V, True{}, Equal.sym(Bool, V, D.list_eq(SLb, SLc), hvl), hv))
  +ev = Equal.trans(List<&2, U32>, SLc, D.slice(D.view(C.BT(cbl, cbt)), U32.to_nat(0), U32.to_nat(cbl)), D.view(C.BT(cbl, cbt)),
    Equal.cong(U32, List<&2, U32>, z => D.slice(D.view(C.BT(cbl, cbt)), U32.to_nat(0), U32.to_nat(z)), n, cbl, en), BF.view_all(cbl, cbt, cbd, okcb))
  Equal.trans(String, NR.chars(SLb), NR.chars(D.view(C.BT(cbl, cbt))), c,
    Equal.cong(List<&2, U32>, String, z => NR.chars(z), SLb, D.view(C.BT(cbl, cbt)), Equal.trans(List<&2, U32>, SLb, SLc, D.view(C.BT(cbl, cbt)), e1, ev)), htx)

# ---------------------------------------------------------------------------
# ref_check from Nat facts
# ---------------------------------------------------------------------------

def rc(+clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +start: Nat, +ref: List<&2, B.Base>, +n: Nat,
  +hn: {List.length(&2, B.Base, ref) == n : Nat},
  +hf: {Nat.is_le(Nat.add(start, n), clen) == True{} : Bool},
  +hc1: {Nat.is_le(off, start) == True{} : Bool},
  +hc2: {Nat.is_le(Nat.add(start, n), Nat.add(off, List.length(&2, B.Base, bases))) == True{} : Bool},
  +he: {B.Bases.eq(List.take(&2, B.Base, List.drop(&2, B.Base, bases, Nat.sub(start, off)), n), ref) == True{} : Bool}) ->
  {J.ref_check(clen, off, bases, start, ref) == Some{True{}} : Maybe<&2, Bool>}:
  +BE = B.Bases.eq(List.take(&2, B.Base, List.drop(&2, B.Base, bases, Nat.sub(start, off)), n), ref)
  %Equal.sym(Nat, List.length(&2, B.Base, ref), n, hn) :
    {J.ref_check.go(Nat.is_le(Nat.add(start, _), clen), Bool.and(Nat.is_le(off, start), Nat.is_le(Nat.add(start, _), Nat.add(off, List.length(&2, B.Base, bases)))), B.Bases.eq(List.take(&2, B.Base, List.drop(&2, B.Base, bases, Nat.sub(start, off)), _), ref)) == Some{True{}} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(start, n), clen), True{}, hf) :
    {J.ref_check.go(_, Bool.and(Nat.is_le(off, start), Nat.is_le(Nat.add(start, n), Nat.add(off, List.length(&2, B.Base, bases)))), BE) == Some{True{}} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Nat.is_le(off, start), True{}, hc1) :
    {J.ref_check.go(True{}, Bool.and(_, Nat.is_le(Nat.add(start, n), Nat.add(off, List.length(&2, B.Base, bases)))), BE) == Some{True{}} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(start, n), Nat.add(off, List.length(&2, B.Base, bases))), True{}, hc2) :
    {J.ref_check.go(True{}, Bool.and(True{}, _), BE) == Some{True{}} : Maybe<&2, Bool>}
  %Equal.sym(Bool, BE, True{}, he) : {J.ref_check.go(True{}, True{}, _) == Some{True{}} : Maybe<&2, Bool>}
  {==}

# ---------------------------------------------------------------------------
# The fast path's POS - 1 and POS - 1 + rl, as Nats
# ---------------------------------------------------------------------------

def WLp(+p: Nat, +e: {Nat.is_eq(p, 0n) == False{} : Bool}) -> {Nat.is_le(1n, p) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, N.true_ne_false(e))
    case 1n+q:
      N.le_zero_l(q)

def tpp(+pos: U32, +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool}) ->
  {U32.to_nat((pos - 1 : U32)) == Nat.sub(U32.to_nat(pos), 1n) : Nat}:
  +h1 = WLp(U32.to_nat(pos), hp)
  U.to_nat_sub_le(pos, 1, Equal.trans(Bool, U32.is_le(1, pos), Nat.is_le(U32.to_nat(1), U32.to_nat(pos)), True{}, U.is_le_to_nat(1, pos), h1))

def tend(+pos: U32, +rl: U32, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +rs: U32,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool}) ->
  {U32.to_nat(((pos - 1 : U32) + rl : U32)) == Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat(rl)) : Nat}:
  +ST = Nat.sub(U32.to_nat(pos), 1n)
  +ep = tpp(pos, hp)
  +hpp = AB.subst(Nat, z => {Nat.is_lt(z, Nat.pow(2n, 31n)) == True{} : Bool}, ST, U32.to_nat((pos - 1 : U32)), Equal.sym(Nat, U32.to_nat((pos - 1 : U32)), ST, ep),
    N.le_lt_trans(ST, U32.to_nat(pos), Nat.pow(2n, 31n), X.sub_le(U32.to_nat(pos), 1n), pos31(pos, hps)))
  +hrl = N.le_trans(U32.to_nat(rl), U32.to_nat(bl), Nat.pow(2n, 31n), X.le_add_r2(U32.to_nat(rs), U32.to_nat(rl), U32.to_nat(bl), hr),
    N.le_trans(U32.to_nat(bl), Nat.mul(4n, Nat.pow(2n, bd)), Nat.pow(2n, 31n), C.ok_len(bl, bt, bd, hok), four_pow(bd, C.ok_d(bl, bt, bd, hok))))
  %ep : {U32.to_nat(((pos - 1 : U32) + rl : U32)) == Nat.add(_, U32.to_nat(rl)) : Nat}
  U.to_nat_add_fits_p((pos - 1 : U32), rl, sum32(U32.to_nat((pos - 1 : U32)), U32.to_nat(rl), hpp, hrl))
