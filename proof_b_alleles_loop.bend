import Base
import ./norm_fast.bend as NF
import ./proof_b_fasteq.bend as FE
import ./proof_b_alleles_list.bend as LS
import ../lawful-bytes/defs.bend as D
import ../lawful-fields/defs.bend as FD
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/fast.bend as FA
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_seq.bend as Q
import ../lawful-bytes/proof_find.bend as F
import ../lawful-bytes/proof_same.bend as S
import ../lawful-bytes/proof_list.bend as BL
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-arrays/proof_tree.bend as P

# The fast path's allele loops (norm_fast.bend) on the mirror C.BT(len, t),
# described by list functions of its view X. Positions are U32 words;
# lemmas state their numbers (U32.to_nat) as Nat.

def X(+len: U32, +t: P.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

# Every byte is an upper-case A, C, G, T or N.
def up(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      NF.is_base(x) && up(t)

# The last element (d if there is none).
def lastb(xs: List<&2, U32>, +d: U32) -> U32:
  match xs:
    case Nil{}:
      d
    case Con{x, t}:
      lastb(t, x)

# The first element (d if there is none).
def headb(xs: List<&2, U32>, +d: U32) -> U32:
  match xs:
    case Nil{}:
      d
    case Con{x, t}:
      x

# Numbers
# =======

law le_u:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}
  {U32.is_le(a, b) == True{} : Bool}

def le_u(a, b, h):
  %Equal.sym(Bool, U32.is_le(a, b), Nat.is_le(U32.to_nat(a), U32.to_nat(b)), U.is_le_to_nat(a, b)) : {_ == True{} : Bool}
  h

law lt_u:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}
  {U32.is_lt(a, b) == True{} : Bool}

def lt_u(a, b, h):
  %Equal.sym(Bool, U32.is_lt(a, b), Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), U.is_lt_to_nat(a, b)) : {_ == True{} : Bool}
  h

law sub_u:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}
  {U32.to_nat((a - b : U32)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

def sub_u(a, b, h):
  U.to_nat_sub_le(a, b, le_u(b, a, h))

# bases
# =====

# r holds byte j; j + n = to.
law bgo:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +to: U32
  for +ok: Bool
  for +x: U32
  for +hn: {Nat.add(U32.to_nat(j), n) == U32.to_nat(to) : Nat}
  for +hto: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {NF.bases.go(n, (C.BT(len, t), C.AT(len, t, j)), j, ok, x) == NF.Bv{C.BT(len, t), Bool.and(ok, up(D.slice(X(len, t), U32.to_nat(j), n))), lastb(D.slice(X(len, t), U32.to_nat(j), n), x)} : NF.Bv}

def bgo(n, len, t, d, j, to, ok, x, hn, hto, h):
  match n:
    case 0n:
      +L = List.drop(&2, U32, X(len, t), U32.to_nat(j))
      %Equal.sym(List<&2, U32>, List.take(&2, U32, L, 0n), Nil{}, Q.take_zero(L)) :
        {NF.Bv{C.BT(len, t), ok, x} == NF.Bv{C.BT(len, t), Bool.and(ok, up(_)), lastb(_, x)} : NF.Bv}
      %Equal.sym(Bool, Bool.and(ok, True{}), ok, LS.and_true(ok)) : {NF.Bv{C.BT(len, t), ok, x} == NF.Bv{C.BT(len, t), _, x} : NF.Bv}
      {==}
    case 1n+k:
      +tj = U32.to_nat(j)
      +VW = X(len, t)
      +y = C.AT(len, t, j)
      +j1 = (j + 1 : U32)
      +hd = C.ok_d(len, t, d, h)
      +hj = F.step_lt(len, j, to, k, hn, hto)
      +hj4 = F.step_lt4(len, t, d, j, h, hj)
      +S1 = D.slice(VW, U32.to_nat(j1), k)
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j1), (C.BT(len, t), C.AT(len, t, j1)), C.at_pair_t(len, t, j1)) :
        {NF.bases.go(k, _, j1, Bool.and(ok, NF.is_base(y)), y) == NF.Bv{C.BT(len, t), Bool.and(ok, up(D.slice(VW, tj, 1n+k))), lastb(D.slice(VW, tj, 1n+k), x)} : NF.Bv}
      %Equal.sym(List<&2, U32>, D.slice(VW, tj, 1n+k), y <> D.slice(VW, Nat.add(tj, 1n), k), S.slice_cons(VW, tj, k, y, F.step_get(len, t, d, j, h, hj))) :
        {NF.bases.go(k, (C.BT(len, t), C.AT(len, t, j1)), j1, Bool.and(ok, NF.is_base(y)), y) == NF.Bv{C.BT(len, t), Bool.and(ok, up(_)), lastb(_, x)} : NF.Bv}
      %C.inc_fits(j, d, hd, hj4) :
        {NF.bases.go(k, (C.BT(len, t), C.AT(len, t, j1)), j1, Bool.and(ok, NF.is_base(y)), y) == NF.Bv{C.BT(len, t), Bool.and(ok, Bool.and(NF.is_base(y), up(D.slice(VW, _, k)))), lastb(D.slice(VW, _, k), y)} : NF.Bv}
      %LS.and_assoc(ok, NF.is_base(y), up(S1)) :
        {NF.bases.go(k, (C.BT(len, t), C.AT(len, t, j1)), j1, Bool.and(ok, NF.is_base(y)), y) == NF.Bv{C.BT(len, t), _, lastb(S1, y)} : NF.Bv}
      bgo(k, len, t, d, j1, to, Bool.and(ok, NF.is_base(y)), y, F.step_n(j, k, to, d, hd, hj4, hn), hto, h)

def BS(+len: U32, +t: P.Tree<U32>, +a: U32, +c: U32) -> List<&2, U32>:
  D.slice(X(len, t), U32.to_nat(a), Nat.sub(U32.to_nat(c), U32.to_nat(a)))

# Bytes from .. to-1: all bases, and the last one (0 if none).
law bases_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {Nat.is_le(U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}
  for +hto: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  {NF.bases(C.BT(len, t), from, to) == NF.Bv{C.BT(len, t), up(BS(len, t, from, to)), lastb(BS(len, t, from, to), 0)} : NF.Bv}

def bases_t(len, t, d, from, to, h, hft, hto):
  +m = Nat.sub(U32.to_nat(to), U32.to_nat(from))
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), from), (C.BT(len, t), C.AT(len, t, from)), C.at_pair_t(len, t, from)) :
    {NF.bases.go(U32.to_nat((to - from : U32)), _, from, True{}, 0) == NF.Bv{C.BT(len, t), up(BS(len, t, from, to)), lastb(BS(len, t, from, to), 0)} : NF.Bv}
  %Equal.sym(Nat, U32.to_nat((to - from : U32)), m, sub_u(to, from, hft)) :
    {NF.bases.go(_, (C.BT(len, t), C.AT(len, t, from)), from, True{}, 0) == NF.Bv{C.BT(len, t), up(BS(len, t, from, to)), lastb(BS(len, t, from, to), 0)} : NF.Bv}
  bgo(m, len, t, d, from, to, True{}, 0, N.le_sub_add(U32.to_nat(from), U32.to_nat(to), hft), hto, h)

# Lists and Nat
# =============

law len_drop:
  for +xs: List<&2, U32>
  for +k: Nat
  {List.length(&2, U32, List.drop(&2, U32, xs, k)) == Nat.sub(List.length(&2, U32, xs), k) : Nat}

def len_drop(xs, k):
  match xs k:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      len_drop(t, p)

law le_sub_r:
  for +i: Nat
  for +k: Nat
  for +m: Nat
  for +h: {Nat.is_le(Nat.add(i, k), m) == True{} : Bool}
  {Nat.is_le(k, Nat.sub(m, i)) == True{} : Bool}

def le_sub_r(i, k, m, h):
  match i m:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, N.sub_zero(m)) : {Nat.is_le(k, _) == True{} : Bool}
      h
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(k, 0n) == True{} : Bool}, LS.ft(h))
    case 1n+p 1n+q:
      le_sub_r(p, k, q, h)

# A slice that fits has its length.
law slice_len:
  for +xs: List<&2, U32>
  for +i: Nat
  for +k: Nat
  for +h: {Nat.is_le(Nat.add(i, k), List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, D.slice(xs, i, k)) == k : Nat}

def slice_len(xs, i, k, h):
  +L = List.drop(&2, U32, xs, i)
  Q.take_length(L, k,
    %Equal.sym(Nat, List.length(&2, U32, L), Nat.sub(List.length(&2, U32, xs), i), len_drop(xs, i)) : {Nat.is_le(k, _) == True{} : Bool}
    le_sub_r(i, k, List.length(&2, U32, xs), h))

law le_antisym:
  for +a: Nat
  for +b: Nat
  for +h1: {Nat.is_le(a, b) == True{} : Bool}
  for +h2: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

def le_antisym(a, b, h1, h2):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, LS.ft(h2))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, LS.ft(h1))
    case 1n+p 1n+q:
      %le_antisym(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

def le_ne.k(+xs: List<&2, U32>, +ys: List<&2, U32>, +b: Bool, +eb: {D.list_eq(xs, ys) == b : Bool},
  +hne: {Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, ys)) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +exy = BL.list_eq_true(xs, ys, eb)
      +ht = {%Equal.sym(List<&2, U32>, xs, ys, exy) : {Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, _)) == False{} : Bool}; hne : {Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, xs)) == False{} : Bool}}
      Empty.absurd({True{} == False{} : Bool}, LS.ft(Equal.trans(Bool, False{}, Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, xs)), True{},
        Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, xs)), False{}, ht), N.eq_refl(List.length(&2, U32, xs)))))

# Lists of different lengths are not equal.
law list_eq_len:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +hne: {Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, ys)) == False{} : Bool}
  {D.list_eq(xs, ys) == False{} : Bool}

def list_eq_len(xs, ys, hne):
  le_ne.k(xs, ys, D.list_eq(xs, ys), {==}, hne)

# eqa
# ===

def SL(+len: U32, +t: P.Tree<U32>, +i: U32, +n: U32) -> List<&2, U32>:
  D.slice(X(len, t), U32.to_nat(i), U32.to_nat(n))

def eqa.k(+len: U32, +t: P.Tree<U32>, +d: Nat, +i: U32, +n: U32, +j: U32, +m: U32, +b: Bool,
  +eb: {U32.is_eq(n, m) == b : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), U32.to_nat(len)) == True{} : Bool},
  +hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(m)), U32.to_nat(len)) == True{} : Bool}) ->
  {NF.eqa.if(b, C.BT(len, t), i, j, n) == (C.BT(len, t), D.list_eq(SL(len, t, i, n), SL(len, t, j, m))) : D.Bytes & Bool}:
  match b:
    case True{}:
      +enm = U.is_eq_true(n, m, eb)
      %enm :
        {BY.same1(C.BT(len, t), i, j, n) == (C.BT(len, t), D.list_eq(SL(len, t, i, n), SL(len, t, j, _))) : D.Bytes & Bool}
      %Equal.sym(D.Bytes & Bool, BY.same1(C.BT(len, t), i, j, n), (C.BT(len, t), Pair.snd(D.Bytes, Bool, BY.same1(C.BT(len, t), i, j, n))), S.same1_pair_t(len, t, i, j, n)) :
        {_ == (C.BT(len, t), D.list_eq(SL(len, t, i, n), SL(len, t, j, n))) : D.Bytes & Bool}
      %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, BY.same1(C.BT(len, t), i, j, n)), D.list_eq(SL(len, t, i, n), SL(len, t, j, n)),
        S.same1_view_t(len, t, d, i, j, n, h, hi, %Equal.sym(U32, n, m, enm) : {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(_)), U32.to_nat(len)) == True{} : Bool}; hj)) :
        {(C.BT(len, t), _) == (C.BT(len, t), D.list_eq(SL(len, t, i, n), SL(len, t, j, n))) : D.Bytes & Bool}
      {==}
    case False{}:
      +VW = X(len, t)
      +hl = Equal.sym(Nat, List.length(&2, U32, VW), U32.to_nat(len), O.view_size_t(len, t, d, h))
      +li = slice_len(VW, U32.to_nat(i), U32.to_nat(n), %hl : {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), _) == True{} : Bool}; hi)
      +lj = slice_len(VW, U32.to_nat(j), U32.to_nat(m), %hl : {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(m)), _) == True{} : Bool}; hj)
      %Equal.sym(Bool, D.list_eq(SL(len, t, i, n), SL(len, t, j, m)), False{}, list_eq_len(SL(len, t, i, n), SL(len, t, j, m),
        %Equal.sym(Nat, List.length(&2, U32, SL(len, t, i, n)), U32.to_nat(n), li) : {Nat.is_eq(_, List.length(&2, U32, SL(len, t, j, m))) == False{} : Bool};
        %Equal.sym(Nat, List.length(&2, U32, SL(len, t, j, m)), U32.to_nat(m), lj) : {Nat.is_eq(U32.to_nat(n), _) == False{} : Bool};
        %U.is_eq_to_nat(n, m) : {_ == False{} : Bool};
        eb)) :
        {(C.BT(len, t), False{}) == (C.BT(len, t), _) : D.Bytes & Bool}
      {==}

# The alleles at i (n bytes) and j (m bytes) are equal.
law eqa_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +i: U32
  for +n: U32
  for +j: U32
  for +m: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), U32.to_nat(len)) == True{} : Bool}
  for +hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(m)), U32.to_nat(len)) == True{} : Bool}
  {NF.eqa(C.BT(len, t), i, n, j, m) == (C.BT(len, t), D.list_eq(SL(len, t, i, n), SL(len, t, j, m))) : D.Bytes & Bool}

def eqa_t(len, t, d, i, n, j, m, h, hi, hj):
  eqa.k(len, t, d, i, n, j, m, U32.is_eq(n, m), {==}, h, hi, hj)

# find
# ====

def FV(+len: U32, +t: P.Tree<U32>, +a: U32, +e: U32) -> U32:
  Pair.snd(D.Bytes, U32, FA.find(C.BT(len, t), a, e, 44))

law find_step:
  for +len: U32
  for +t: P.Tree<U32>
  for +a: U32
  for +e: U32
  {FA.find(C.BT(len, t), a, e, 44) == (C.BT(len, t), FV(len, t, a, e)) : D.Bytes & U32}

def find_step(len, t, a, e):
  FE.find_pair(C.BT(len, t), a, e, 44)

law fv_val:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  {U32.to_nat(FV(len, t, a, e)) == D.first(X(len, t), U32.to_nat(a), U32.to_nat(e), 44) : Nat}

def fv_val(len, t, d, a, e, h, hae, hel):
  Equal.trans(Nat, U32.to_nat(FV(len, t, a, e)), U32.to_nat(Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), a, e, 44))), D.first(X(len, t), U32.to_nat(a), U32.to_nat(e), 44),
    Equal.cong(D.Bytes & U32, Nat, r => U32.to_nat(Pair.snd(D.Bytes, U32, r)), FA.find(C.BT(len, t), a, e, 44), BY.find(C.BT(len, t), a, e, 44), FE.find_eq(C.BT(len, t), d, a, e, 44, h, le_u(a, e, hae), hel, {==})),
    F.find_view_t(len, t, d, a, e, 44, h, le_u(a, e, hae), hel, {==}))

law len_x:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {U32.to_nat(len) == List.length(&2, U32, X(len, t)) : Nat}

def len_x(len, t, d, h):
  Equal.sym(Nat, List.length(&2, U32, X(len, t)), U32.to_nat(len), O.view_size_t(len, t, d, h))

# a <= the answer <= e.
law fv_range:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  {Bool.and(Nat.is_le(U32.to_nat(a), U32.to_nat(FV(len, t, a, e))), Nat.is_le(U32.to_nat(FV(len, t, a, e)), U32.to_nat(e))) == True{} : Bool}

def fv_range(len, t, d, a, e, h, hae, hel):
  %Equal.sym(Nat, U32.to_nat(FV(len, t, a, e)), D.first(X(len, t), U32.to_nat(a), U32.to_nat(e), 44), fv_val(len, t, d, a, e, h, hae, hel)) :
    {Bool.and(Nat.is_le(U32.to_nat(a), _), Nat.is_le(_, U32.to_nat(e))) == True{} : Bool}
  BL.first_range(X(len, t), U32.to_nat(a), U32.to_nat(e), 44, hae, %len_x(len, t, d, h) : {Nat.is_le(U32.to_nat(e), _) == True{} : Bool}; hel)

def hg.k(m: Maybe<&2, U32>, +c: U32, +h: {D.is_some(m, c) == True{} : Bool}) -> {m == Some{c} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{c} : Maybe<&2, U32>}, LS.ft(h))
    case Some{+x}:
      %U.is_eq_true(x, c, h) : {Some{x} == Some{_} : Maybe<&2, U32>}
      {==}

law has_get:
  for +xs: List<&2, U32>
  for +k: Nat
  for +c: U32
  for +h: {D.has(xs, k, c) == True{} : Bool}
  {List.get(&2, U32, xs, k) == Some{c} : Maybe<&2, U32>}

def has_get(xs, k, c, h):
  hg.k(List.get(&2, U32, xs, k), c, h)

# Below e, the answer is a comma.
law fv_hit:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(FV(len, t, a, e)), U32.to_nat(e)) == True{} : Bool}
  {List.get(&2, U32, X(len, t), U32.to_nat(FV(len, t, a, e))) == Some{44} : Maybe<&2, U32>}

def fv_hit(len, t, d, a, e, h, hae, hel, hlt):
  +VW = X(len, t)
  +fst = D.first(VW, U32.to_nat(a), U32.to_nat(e), 44)
  +ev = fv_val(len, t, d, a, e, h, hae, hel)
  %Equal.sym(Nat, U32.to_nat(FV(len, t, a, e)), fst, ev) : {List.get(&2, U32, VW, _) == Some{44} : Maybe<&2, U32>}
  has_get(VW, fst, 44, BL.first_hit(VW, U32.to_nat(a), U32.to_nat(e), 44, hae, %len_x(len, t, d, h) : {Nat.is_le(U32.to_nat(e), _) == True{} : Bool}; hel,
    %ev : {Nat.is_lt(_, U32.to_nat(e)) == True{} : Bool}; hlt))

# The pieces of a slice
# =====================

def LL() -> Data:
  List<&2, List<&2, U32>>

# x is equal to one of the lists in E.
def memb(+x: List<&2, U32>, E: LL()) -> Bool:
  match E:
    case Nil{}:
      False{}
    case Con{y, t}:
      D.list_eq(x, y) || memb(x, t)

# The comma-separated pieces of bytes a .. e-1.
def PS(+len: U32, +t: P.Tree<U32>, +a: U32, +e: U32) -> LL():
  FD.split(BS(len, t, a, e), 44)

def TS(+len: U32, +t: P.Tree<U32>, +c: U32, +e: U32) -> LL():
  LS.tsplit(BS(len, t, c, e), 44)

law ps_first:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  {PS(len, t, a, e) == Con{BS(len, t, a, FV(len, t, a, e)), TS(len, t, FV(len, t, a, e), e)} : LL()}

def ps_first(len, t, d, a, e, h, hae, hel):
  +VW = X(len, t)
  +na = U32.to_nat(a)
  +ne = U32.to_nat(e)
  +ev = fv_val(len, t, d, a, e, h, hae, hel)
  %Equal.sym(Nat, U32.to_nat(FV(len, t, a, e)), D.first(VW, na, ne, 44), ev) : {PS(len, t, a, e) == Con{D.slice(VW, na, Nat.sub(_, na)), LS.tsplit(D.slice(VW, _, Nat.sub(ne, _)), 44)} : LL()}
  LS.spl(VW, na, ne, 44)

# A word below len steps up by one.
law inc_len:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_lt(U32.to_nat(c), U32.to_nat(len)) == True{} : Bool}
  {U32.to_nat((c + 1 : U32)) == Nat.add(U32.to_nat(c), 1n) : Nat}

def inc_len(len, t, d, c, h, hc):
  C.inc_fits(c, d, C.ok_d(len, t, d, h), F.step_lt4(len, t, d, c, h, hc))

# The pieces after a comma at c < e.
law ts_next:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +c: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(c), U32.to_nat(e)) == True{} : Bool}
  for +hg: {List.get(&2, U32, X(len, t), U32.to_nat(c)) == Some{44} : Maybe<&2, U32>}
  {TS(len, t, c, e) == PS(len, t, (c + 1 : U32), e) : LL()}

def ts_next(len, t, d, c, e, h, hel, hlt, hg):
  +VW = X(len, t)
  +nc = U32.to_nat(c)
  +ne = U32.to_nat(e)
  %Equal.sym(Nat, U32.to_nat((c + 1 : U32)), Nat.add(nc, 1n), inc_len(len, t, d, c, h, N.lt_le_trans(nc, ne, U32.to_nat(len), hlt, hel))) :
    {TS(len, t, c, e) == FD.split(D.slice(VW, _, Nat.sub(ne, _)), 44) : LL()}
  LS.ts_lt(VW, nc, ne, 44, hlt, hg)

law ts_last:
  for +len: U32
  for +t: P.Tree<U32>
  for +c: U32
  for +e: U32
  for +hce: {U32.to_nat(c) == U32.to_nat(e) : Nat}
  {TS(len, t, c, e) == Nil{} : LL()}

def ts_last(len, t, c, e, hce):
  %Equal.sym(Nat, U32.to_nat(c), U32.to_nat(e), hce) : {LS.tsplit(D.slice(X(len, t), _, Nat.sub(U32.to_nat(e), _)), 44) == Nil{} : LL()}
  LS.ts_eq(X(len, t), U32.to_nat(e), 44)

law ps_len0:
  for +ys: List<&2, U32>
  {Nat.is_le(List.length(&2, List<&2, U32>, FD.split(ys, 44)), 0n) == False{} : Bool}

def ps_len0(ys):
  %Equal.sym(LL(), FD.split(ys, 44), LS.SR(ys, 44), LS.split_run(ys, 44)) : {Nat.is_le(List.length(&2, List<&2, U32>, _), 0n) == False{} : Bool}
  {==}

# dup
# ===

law cle:
  for +a: Nat
  for +c: Nat
  for +e: Nat
  for +hr: {Bool.and(Nat.is_le(a, c), Nat.is_le(c, e)) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def cle(a, c, e, hr):
  LS.and_l(Nat.is_le(a, c), Nat.is_le(c, e), hr)

law cre:
  for +a: Nat
  for +c: Nat
  for +e: Nat
  for +hr: {Bool.and(Nat.is_le(a, c), Nat.is_le(c, e)) == True{} : Bool}
  {Nat.is_le(c, e) == True{} : Bool}

def cre(a, c, e, hr):
  LS.and_r(Nat.is_le(a, c), Nat.is_le(c, e), hr)

# a + (c - a) <= len, for a <= c <= e <= len.
law fit_ac:
  for +a: U32
  for +c: U32
  for +e: U32
  for +len: U32
  for +hr: {Bool.and(Nat.is_le(U32.to_nat(a), U32.to_nat(c)), Nat.is_le(U32.to_nat(c), U32.to_nat(e))) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat((c - a : U32))), U32.to_nat(len)) == True{} : Bool}

def fit_ac(a, c, e, len, hr, hel):
  +na = U32.to_nat(a)
  +nc = U32.to_nat(c)
  +ne = U32.to_nat(e)
  +hac = cle(na, nc, ne, hr)
  %Equal.sym(Nat, U32.to_nat((c - a : U32)), Nat.sub(nc, na), sub_u(c, a, hac)) : {Nat.is_le(Nat.add(na, _), U32.to_nat(len)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(na, Nat.sub(nc, na)), nc, N.le_sub_add(na, nc, hac)) : {Nat.is_le(_, U32.to_nat(len)) == True{} : Bool}
  N.le_trans(nc, ne, U32.to_nat(len), cre(na, nc, ne, hr), hel)

def EQD(+len: U32, +t: P.Tree<U32>, +x: U32, +lx: U32, +a: U32, +e: U32) -> Bool:
  D.list_eq(SL(len, t, x, lx), BS(len, t, a, FV(len, t, a, e)))

def DNX(+k: Nat, +len: U32, +t: P.Tree<U32>, +x: U32, +lx: U32, +a: U32, +e: U32) -> D.Bytes & Bool:
  NF.dup.go(k, NF.Dp{C.BT(len, t), x, lx, (FV(len, t, a, e) + 1 : U32), e, EQD(len, t, x, lx, a, e), Bool.and(Bool.not(EQD(len, t, x, lx, a, e)), U32.is_lt(FV(len, t, a, e), e))})

law dstep:
  for +k: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +x: U32
  for +lx: U32
  for +a: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hx: {Nat.is_le(Nat.add(U32.to_nat(x), U32.to_nat(lx)), U32.to_nat(len)) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  {NF.dup.go(1n+k, NF.Dp{C.BT(len, t), x, lx, a, e, False{}, True{}}) == DNX(k, len, t, x, lx, a, e) : D.Bytes & Bool}

def dstep(k, len, t, d, x, lx, a, e, h, hx, hae, hel):
  +c = FV(len, t, a, e)
  +hr = fv_range(len, t, d, a, e, h, hae, hel)
  %Equal.sym(D.Bytes & U32, FA.find(C.BT(len, t), a, e, 44), (C.BT(len, t), c), find_step(len, t, a, e)) :
    {NF.dup.go(k, NF.dup.c(x, lx, a, e, _)) == DNX(k, len, t, x, lx, a, e) : D.Bytes & Bool}
  %Equal.sym(D.Bytes & Bool, NF.eqa(C.BT(len, t), x, lx, a, (c - a : U32)), (C.BT(len, t), D.list_eq(SL(len, t, x, lx), SL(len, t, a, (c - a : U32)))),
    eqa_t(len, t, d, x, lx, a, (c - a : U32), h, hx, fit_ac(a, c, e, len, hr, hel))) :
    {NF.dup.go(k, NF.dup.eq(x, lx, e, c, _)) == DNX(k, len, t, x, lx, a, e) : D.Bytes & Bool}
  %Equal.sym(Nat, U32.to_nat((c - a : U32)), Nat.sub(U32.to_nat(c), U32.to_nat(a)), sub_u(c, a, cle(U32.to_nat(a), U32.to_nat(c), U32.to_nat(e), hr))) :
    {NF.dup.go(k, NF.dup.eq(x, lx, e, c, (C.BT(len, t), D.list_eq(SL(len, t, x, lx), D.slice(X(len, t), U32.to_nat(a), _))))) == DNX(k, len, t, x, lx, a, e) : D.Bytes & Bool}
  {==}

law lt_n:
  for +a: U32
  for +b: U32
  for +h: {U32.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}

def lt_n(a, b, h):
  %U.is_lt_to_nat(a, b) : {_ == True{} : Bool}
  h

law nlt_n:
  for +a: U32
  for +b: U32
  for +h: {U32.is_lt(a, b) == False{} : Bool}
  {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == False{} : Bool}

def nlt_n(a, b, h):
  %U.is_lt_to_nat(a, b) : {_ == False{} : Bool}
  h

# Not below e, and at most e: the answer is e.
law fv_end:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  for +hn: {U32.is_lt(FV(len, t, a, e), e) == False{} : Bool}
  {U32.to_nat(FV(len, t, a, e)) == U32.to_nat(e) : Nat}

def fv_end(len, t, d, a, e, h, hae, hel, hn):
  +nc = U32.to_nat(FV(len, t, a, e))
  +ne = U32.to_nat(e)
  le_antisym(nc, ne, cre(U32.to_nat(a), nc, ne, fv_range(len, t, d, a, e, h, hae, hel)), N.not_lt_le(nc, ne, nlt_n(FV(len, t, a, e), e, hn)))

def dgo.k(+q: Bool, +b: Bool, +k: Nat, +len: U32, +t: P.Tree<U32>, +d: Nat, +x: U32, +lx: U32, +a: U32, +e: U32,
  +eb: {U32.is_lt(FV(len, t, a, e), e) == b : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool},
  +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool},
  ih: {b == True{} : Bool} -> {NF.dup.go(k, NF.Dp{C.BT(len, t), x, lx, (FV(len, t, a, e) + 1 : U32), e, False{}, True{}}) == (C.BT(len, t), memb(SL(len, t, x, lx), PS(len, t, (FV(len, t, a, e) + 1 : U32), e))) : D.Bytes & Bool}) ->
  {NF.dup.go(k, NF.Dp{C.BT(len, t), x, lx, (FV(len, t, a, e) + 1 : U32), e, q, Bool.and(Bool.not(q), b)}) == (C.BT(len, t), Bool.or(q, memb(SL(len, t, x, lx), TS(len, t, FV(len, t, a, e), e)))) : D.Bytes & Bool}:
  match q b k:
    case True{} _ 0n:
      {==}
    case True{} _ 1n+j:
      {==}
    case False{} True{} _:
      +c = FV(len, t, a, e)
      +hlt = lt_n(c, e, eb)
      %Equal.sym(LL(), TS(len, t, c, e), PS(len, t, (c + 1 : U32), e), ts_next(len, t, d, c, e, h, hel, hlt, fv_hit(len, t, d, a, e, h, hae, hel, hlt))) :
        {NF.dup.go(k, NF.Dp{C.BT(len, t), x, lx, (c + 1 : U32), e, False{}, True{}}) == (C.BT(len, t), memb(SL(len, t, x, lx), _)) : D.Bytes & Bool}
      ih({==})
    case False{} False{} 0n:
      %Equal.sym(LL(), TS(len, t, FV(len, t, a, e), e), Nil{}, ts_last(len, t, FV(len, t, a, e), e, fv_end(len, t, d, a, e, h, hae, hel, eb))) :
        {(C.BT(len, t), False{}) == (C.BT(len, t), memb(SL(len, t, x, lx), _)) : D.Bytes & Bool}
      {==}
    case False{} False{} 1n+j:
      %Equal.sym(LL(), TS(len, t, FV(len, t, a, e), e), Nil{}, ts_last(len, t, FV(len, t, a, e), e, fv_end(len, t, d, a, e, h, hae, hel, eb))) :
        {(C.BT(len, t), False{}) == (C.BT(len, t), memb(SL(len, t, x, lx), _)) : D.Bytes & Bool}
      {==}

# The allele at x (lx bytes) against the pieces of a .. e-1 (with enough
# fuel): it is one of them.
law dgo:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +x: U32
  for +lx: U32
  for +a: U32
  for +e: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hx: {Nat.is_le(Nat.add(U32.to_nat(x), U32.to_nat(lx)), U32.to_nat(len)) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}
  for +hn: {Nat.is_le(List.length(&2, List<&2, U32>, PS(len, t, a, e)), n) == True{} : Bool}
  {NF.dup.go(n, NF.Dp{C.BT(len, t), x, lx, a, e, False{}, True{}}) == (C.BT(len, t), memb(SL(len, t, x, lx), PS(len, t, a, e))) : D.Bytes & Bool}

def dgo(n, len, t, d, x, lx, a, e, h, hx, hae, hel, hn):
  match n:
    case 0n:
      Empty.absurd({NF.dup.go(0n, NF.Dp{C.BT(len, t), x, lx, a, e, False{}, True{}}) == (C.BT(len, t), memb(SL(len, t, x, lx), PS(len, t, a, e))) : D.Bytes & Bool},
        LS.ft(Equal.trans(Bool, False{}, Nat.is_le(List.length(&2, List<&2, U32>, PS(len, t, a, e)), 0n), True{},
          Equal.sym(Bool, Nat.is_le(List.length(&2, List<&2, U32>, PS(len, t, a, e)), 0n), False{}, ps_len0(BS(len, t, a, e))), hn)))
    case 1n+k:
      +c = FV(len, t, a, e)
      +XQ = SL(len, t, x, lx)
      %Equal.sym(D.Bytes & Bool, NF.dup.go(1n+k, NF.Dp{C.BT(len, t), x, lx, a, e, False{}, True{}}), DNX(k, len, t, x, lx, a, e), dstep(k, len, t, d, x, lx, a, e, h, hx, hae, hel)) :
        {_ == (C.BT(len, t), memb(XQ, PS(len, t, a, e))) : D.Bytes & Bool}
      %Equal.sym(LL(), PS(len, t, a, e), Con{BS(len, t, a, c), TS(len, t, c, e)}, ps_first(len, t, d, a, e, h, hae, hel)) :
        {DNX(k, len, t, x, lx, a, e) == (C.BT(len, t), memb(XQ, _)) : D.Bytes & Bool}
      dgo.k(EQD(len, t, x, lx, a, e), U32.is_lt(c, e), k, len, t, d, x, lx, a, e, {==}, h, hae, hel,
        +hl => dgo(k, len, t, d, x, lx, (c + 1 : U32), e, h, hx,
          %Equal.sym(Nat, U32.to_nat((c + 1 : U32)), Nat.add(U32.to_nat(c), 1n), inc_len(len, t, d, c, h, N.lt_le_trans(U32.to_nat(c), U32.to_nat(e), U32.to_nat(len), lt_n(c, e, hl), hel))) :
            {Nat.is_le(_, U32.to_nat(e)) == True{} : Bool};
          C.succ_le(U32.to_nat(c), U32.to_nat(e), lt_n(c, e, hl)),
          hel,
          %ts_next(len, t, d, c, e, h, hel, lt_n(c, e, hl), fv_hit(len, t, d, a, e, h, hae, hel, lt_n(c, e, hl))) :
            {Nat.is_le(List.length(&2, List<&2, U32>, _), k) == True{} : Bool};
          %ps_first(len, t, d, a, e, h, hae, hel) :
            {Nat.is_le(List.length(&2, List<&2, U32>, _), 1n+k) == True{} : Bool};
          hn))

# alts
# ====

def AL(+s3: U32, +l3: U32, +f3: U32, +z3: U32, +s4: U32, +e4: U32) -> NF.Al:
  NF.Al{s3, l3, f3, z3, s4, e4}

# One ALT allele a .. c-1 (c the next comma or e4) passes: all bases, not
# empty, not REF, not an earlier one (in E).
def OK3(+len: U32, +t: P.Tree<U32>, +s3: U32, +l3: U32, +a: U32, +e4: U32, +E: LL()) -> Bool:
  Bool.and(Bool.and(Bool.and(up(BS(len, t, a, FV(len, t, a, e4))), U32.is_lt(a, FV(len, t, a, e4))), Bool.not(D.list_eq(BS(len, t, a, FV(len, t, a, e4)), SL(len, t, s3, l3)))), Bool.not(memb(BS(len, t, a, FV(len, t, a, e4)), E)))

def LN(+len: U32, +t: P.Tree<U32>, +z3: U32, +a: U32, +e4: U32, L: Bool) -> Bool:
  Bool.and(L, U32.is_eq(lastb(BS(len, t, a, FV(len, t, a, e4)), 0), z3))

def FN(+len: U32, +t: P.Tree<U32>, +f3: U32, +a: U32, +e4: U32, Fi: Bool) -> Bool:
  Bool.and(Fi, U32.is_eq(C.AT(len, t, a), f3))

def GN(+len: U32, +t: P.Tree<U32>, +a: U32, +e4: U32, G: Bool) -> Bool:
  Bool.and(G, U32.is_le(2, (FV(len, t, a, e4) - a : U32)))

# The state after the allele at a.
def ANX(+k: Nat, +len: U32, +t: P.Tree<U32>, +s3: U32, +l3: U32, +f3: U32, +z3: U32, +s4: U32, +e4: U32, +a: U32, +E: LL(), +L: Bool, +Fi: Bool, +G: Bool) -> D.Bytes & Bool:
  NF.alts.go(k, NF.As{C.BT(len, t), AL(s3, l3, f3, z3, s4, e4), (FV(len, t, a, e4) + 1 : U32), OK3(len, t, s3, l3, a, e4, E),
    LN(len, t, z3, a, e4, L), FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G), Bool.and(OK3(len, t, s3, l3, a, e4, E), U32.is_lt(FV(len, t, a, e4), e4))})

law astep:
  for +k: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s3: U32
  for +l3: U32
  for +f3: U32
  for +z3: U32
  for +s4: U32
  for +e4: U32
  for +a: U32
  for +ok: Bool
  for +L: Bool
  for +Fi: Bool
  for +G: Bool
  for +E: LL()
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +h3: {Nat.is_le(Nat.add(U32.to_nat(s3), U32.to_nat(l3)), U32.to_nat(len)) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hD: {NF.dup(U32.is_lt(s4, a), C.BT(len, t), a, (FV(len, t, a, e4) - a : U32), s4, (a - 1 : U32)) == (C.BT(len, t), memb(BS(len, t, a, FV(len, t, a, e4)), E)) : D.Bytes & Bool}
  {NF.alts.go(1n+k, NF.As{C.BT(len, t), AL(s3, l3, f3, z3, s4, e4), a, ok, L, Fi, G, True{}}) == ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G) : D.Bytes & Bool}

def astep(k, len, t, d, s3, l3, f3, z3, s4, e4, a, ok, L, Fi, G, E, h, h3, hae, hel, hD):
  +c = FV(len, t, a, e4)
  +A = AL(s3, l3, f3, z3, s4, e4)
  +q = BS(len, t, a, c)
  +R = SL(len, t, s3, l3)
  +hr = fv_range(len, t, d, a, e4, h, hae, hel)
  +hac = cle(U32.to_nat(a), U32.to_nat(c), U32.to_nat(e4), hr)
  +hcl = N.le_trans(U32.to_nat(c), U32.to_nat(e4), U32.to_nat(len), cre(U32.to_nat(a), U32.to_nat(c), U32.to_nat(e4), hr), hel)
  %Equal.sym(D.Bytes & U32, FA.find(C.BT(len, t), a, e4, 44), (C.BT(len, t), c), find_step(len, t, a, e4)) :
    {NF.alts.go(k, NF.alts.c(A, a, L, Fi, G, _)) == ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G) : D.Bytes & Bool}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), a), (C.BT(len, t), C.AT(len, t, a)), C.at_pair_t(len, t, a)) :
    {NF.alts.go(k, NF.alts.ab(A, c, NF.alt.first(A, a, c, L, Fi, G, _))) == ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G) : D.Bytes & Bool}
  %Equal.sym(NF.Bv, NF.bases(C.BT(len, t), a, c), NF.Bv{C.BT(len, t), up(q), lastb(q, 0)}, bases_t(len, t, d, a, c, h, hac, hcl)) :
    {NF.alts.go(k, NF.alts.ab(A, c, NF.alt.bases(A, a, c, C.AT(len, t, a), L, Fi, G, _))) == ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G) : D.Bytes & Bool}
  %Equal.sym(D.Bytes & Bool, NF.eqa(C.BT(len, t), a, (c - a : U32), s3, l3), (C.BT(len, t), D.list_eq(SL(len, t, a, (c - a : U32)), R)),
    eqa_t(len, t, d, a, (c - a : U32), s3, l3, h, fit_ac(a, c, e4, len, hr, hel), h3)) :
    {NF.alts.go(k, NF.alts.ab(A, c, NF.alt.dup(A, a, c, Bool.and(up(q), U32.is_lt(a, c)), C.AT(len, t, a), lastb(q, 0), L, Fi, G, _))) == ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G) : D.Bytes & Bool}
  %Equal.sym(Nat, U32.to_nat((c - a : U32)), Nat.sub(U32.to_nat(c), U32.to_nat(a)), sub_u(c, a, hac)) :
    {NF.alts.go(k, NF.alts.ab(A, c, NF.alt.dup(A, a, c, Bool.and(up(q), U32.is_lt(a, c)), C.AT(len, t, a), lastb(q, 0), L, Fi, G, (C.BT(len, t), D.list_eq(D.slice(X(len, t), U32.to_nat(a), _), R))))) == ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G) : D.Bytes & Bool}
  %Equal.sym(D.Bytes & Bool, NF.dup(U32.is_lt(s4, a), C.BT(len, t), a, (c - a : U32), s4, (a - 1 : U32)), (C.BT(len, t), memb(q, E)), hD) :
    {NF.alts.go(k, NF.alts.ab(A, c, NF.alt.fin(A, a, c, Bool.and(Bool.and(up(q), U32.is_lt(a, c)), Bool.not(D.list_eq(q, R))), C.AT(len, t, a), lastb(q, 0), L, Fi, G, _))) == ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G) : D.Bytes & Bool}
  {==}

# What the alleles pass, as list functions
# ========================================

# One ALT allele q (E: the earlier ones, REF first): all bases, not empty,
# not an earlier one.
def okq(+q: List<&2, U32>, E: LL()) -> Bool:
  Bool.and(Bool.and(up(q), Nat.is_lt(0n, List.length(&2, U32, q))), Bool.not(memb(q, E)))

# The ALT alleles ps pass, and then the flags pass (not all ending with z3;
# not all starting with f3 and all long).
def spec(ps: LL(), +E: LL(), +z3: U32, +f3: U32, L: Bool, Fi: Bool, G: Bool) -> Bool:
  match ps:
    case Nil{}:
      Bool.and(Bool.not(L), Bool.not(Bool.and(Fi, G)))
    case Con{+q, t}:
      Bool.and(okq(q, E), spec(t, LS.lapp(E, [q]), z3, f3, Bool.and(L, U32.is_eq(lastb(q, 0), z3)), Bool.and(Fi, U32.is_eq(headb(q, 0), f3)), Bool.and(G, Nat.is_le(2n, List.length(&2, U32, q)))))

def pdisc(p: D.Bytes & Bool) -> Type:
  match p:
    case (b, x):
      LS.bdisc(x)

law pft:
  for -b1: D.Bytes
  for -b2: D.Bytes
  for e: {(b1, False{}) == (b2, True{}) : D.Bytes & Bool}
  Empty

def pft(b1, b2, e):
  %e : pdisc(_)
  Unit{}

law psnd:
  for -b1: D.Bytes
  for -b2: D.Bytes
  for +x: Bool
  for e: {(b1, x) == (b2, True{}) : D.Bytes & Bool}
  {x == True{} : Bool}

def psnd(b1, b2, x, e):
  Equal.cong(D.Bytes & Bool, Bool, p => Pair.snd(D.Bytes, Bool, p), (b1, x), (b2, True{}), e)

# Facts about one piece a .. c-1
# ==============================

law len_bs:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hac: {Nat.is_le(U32.to_nat(a), U32.to_nat(c)) == True{} : Bool}
  for +hcl: {Nat.is_le(U32.to_nat(c), U32.to_nat(len)) == True{} : Bool}
  {List.length(&2, U32, BS(len, t, a, c)) == Nat.sub(U32.to_nat(c), U32.to_nat(a)) : Nat}

def len_bs(len, t, d, a, c, h, hac, hcl):
  +na = U32.to_nat(a)
  +nc = U32.to_nat(c)
  slice_len(X(len, t), na, Nat.sub(nc, na),
    %Equal.sym(Nat, Nat.add(na, Nat.sub(nc, na)), nc, N.le_sub_add(na, nc, hac)) : {Nat.is_le(_, List.length(&2, U32, X(len, t))) == True{} : Bool};
    %len_x(len, t, d, h) : {Nat.is_le(nc, _) == True{} : Bool};
    hcl)

law pos_sub:
  for +a: Nat
  for +c: Nat
  for +h: {Nat.is_lt(a, c) == True{} : Bool}
  {Nat.is_lt(0n, Nat.sub(c, a)) == True{} : Bool}

def pos_sub(a, c, h):
  %Equal.sym(Nat, Nat.sub(c, a), 1n+Nat.sub(c, Nat.add(a, 1n)), LS.sub_lt(c, a, h)) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

law hd_at:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hac: {Nat.is_lt(U32.to_nat(a), U32.to_nat(c)) == True{} : Bool}
  for +hcl: {Nat.is_le(U32.to_nat(c), U32.to_nat(len)) == True{} : Bool}
  {headb(BS(len, t, a, c), 0) == C.AT(len, t, a) : U32}

def hd_at(len, t, d, a, c, h, hac, hcl):
  +na = U32.to_nat(a)
  +nc = U32.to_nat(c)
  +k = Nat.sub(nc, Nat.add(na, 1n))
  %Equal.sym(Nat, Nat.sub(nc, na), 1n+k, LS.sub_lt(nc, na, hac)) : {headb(D.slice(X(len, t), na, _), 0) == C.AT(len, t, a) : U32}
  %Equal.sym(List<&2, U32>, D.slice(X(len, t), na, 1n+k), C.AT(len, t, a) <> D.slice(X(len, t), Nat.add(na, 1n), k),
    S.slice_cons(X(len, t), na, k, C.AT(len, t, a), F.step_get(len, t, d, a, h, N.lt_le_trans(na, nc, U32.to_nat(len), hac, hcl)))) :
    {headb(_, 0) == C.AT(len, t, a) : U32}
  {==}

law ge2:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hac: {Nat.is_le(U32.to_nat(a), U32.to_nat(c)) == True{} : Bool}
  for +hcl: {Nat.is_le(U32.to_nat(c), U32.to_nat(len)) == True{} : Bool}
  {Nat.is_le(2n, List.length(&2, U32, BS(len, t, a, c))) == U32.is_le(2, (c - a : U32)) : Bool}

def ge2(len, t, d, a, c, h, hac, hcl):
  %Equal.sym(Nat, List.length(&2, U32, BS(len, t, a, c)), Nat.sub(U32.to_nat(c), U32.to_nat(a)), len_bs(len, t, d, a, c, h, hac, hcl)) :
    {Nat.is_le(2n, _) == U32.is_le(2, (c - a : U32)) : Bool}
  %Equal.sym(Bool, U32.is_le(2, (c - a : U32)), Nat.is_le(U32.to_nat(2), U32.to_nat((c - a : U32))), U.is_le_to_nat(2, (c - a : U32))) : {Nat.is_le(2n, Nat.sub(U32.to_nat(c), U32.to_nat(a))) == _ : Bool}
  %Equal.sym(Nat, U32.to_nat((c - a : U32)), Nat.sub(U32.to_nat(c), U32.to_nat(a)), sub_u(c, a, hac)) : {Nat.is_le(2n, Nat.sub(U32.to_nat(c), U32.to_nat(a))) == Nat.is_le(2n, _) : Bool}
  {==}

law okq_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s3: U32
  for +l3: U32
  for +a: U32
  for +e4: U32
  for +E: LL()
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +eo: {OK3(len, t, s3, l3, a, e4, E) == True{} : Bool}
  {okq(BS(len, t, a, FV(len, t, a, e4)), Con{SL(len, t, s3, l3), E}) == True{} : Bool}

def okq_t(len, t, d, s3, l3, a, e4, E, h, hae, hel, eo):
  +c = FV(len, t, a, e4)
  +q = BS(len, t, a, c)
  +R = SL(len, t, s3, l3)
  +U0 = up(q)
  +LTq = U32.is_lt(a, c)
  +NR = Bool.not(D.list_eq(q, R))
  +NM = Bool.not(memb(q, E))
  +e3 = LS.and_l(Bool.and(Bool.and(U0, LTq), NR), NM, eo)
  +em = LS.not_t(memb(q, E), LS.and_r(Bool.and(Bool.and(U0, LTq), NR), NM, eo))
  +e2 = LS.and_l(Bool.and(U0, LTq), NR, e3)
  +er = LS.not_t(D.list_eq(q, R), LS.and_r(Bool.and(U0, LTq), NR, e3))
  +eu = LS.and_l(U0, LTq, e2)
  +hlt = lt_n(a, c, LS.and_r(U0, LTq, e2))
  +hr = fv_range(len, t, d, a, e4, h, hae, hel)
  +hcl = N.le_trans(U32.to_nat(c), U32.to_nat(e4), U32.to_nat(len), cre(U32.to_nat(a), U32.to_nat(c), U32.to_nat(e4), hr), hel)
  +el = Equal.trans(Bool, Nat.is_lt(0n, List.length(&2, U32, q)), Nat.is_lt(0n, Nat.sub(U32.to_nat(c), U32.to_nat(a))), True{},
    %Equal.sym(Nat, List.length(&2, U32, q), Nat.sub(U32.to_nat(c), U32.to_nat(a)), len_bs(len, t, d, a, c, h, cle(U32.to_nat(a), U32.to_nat(c), U32.to_nat(e4), hr), hcl)) : {Nat.is_lt(0n, _) == Nat.is_lt(0n, Nat.sub(U32.to_nat(c), U32.to_nat(a))) : Bool}; {==},
    pos_sub(U32.to_nat(a), U32.to_nat(c), hlt))
  %Equal.sym(Bool, U0, True{}, eu) : {Bool.and(Bool.and(_, Nat.is_lt(0n, List.length(&2, U32, q))), Bool.not(Bool.or(D.list_eq(q, R), memb(q, E)))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(0n, List.length(&2, U32, q)), True{}, el) : {Bool.and(Bool.and(True{}, _), Bool.not(Bool.or(D.list_eq(q, R), memb(q, E)))) == True{} : Bool}
  %Equal.sym(Bool, D.list_eq(q, R), False{}, er) : {Bool.not(Bool.or(_, memb(q, E))) == True{} : Bool}
  %Equal.sym(Bool, memb(q, E), False{}, em) : {Bool.not(_) == True{} : Bool}
  {==}

# The earlier pieces
# ==================

law dec_inc:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_lt(U32.to_nat(c), U32.to_nat(len)) == True{} : Bool}
  {U32.to_nat(((c + 1 : U32) - 1 : U32)) == U32.to_nat(c) : Nat}

def dec_inc(len, t, d, c, h, hc):
  +nc = U32.to_nat(c)
  +ei = inc_len(len, t, d, c, h, hc)
  +c1 = (c + 1 : U32)
  +es = Equal.sym(Nat, U32.to_nat(c1), Nat.add(nc, 1n), ei)
  %Equal.sym(Nat, U32.to_nat((c1 - 1 : U32)), Nat.sub(U32.to_nat(c1), U32.to_nat(1)), sub_u(c1, 1, %es : {Nat.is_le(1n, _) == True{} : Bool}; N.le_add_l(1n, nc))) : {_ == nc : Nat}
  %es : {Nat.sub(_, 1n) == nc : Nat}
  N.sub_add(nc, 1n)

law sub1_add1:
  for +a: Nat
  for +h: {Nat.is_lt(0n, a) == True{} : Bool}
  {Nat.add(Nat.sub(a, 1n), 1n) == a : Nat}

def sub1_add1(a, h):
  match a:
    case 0n:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n), 1n) == 0n : Nat}, LS.ft(h))
    case 1n+m:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, N.sub_zero(m)) : {Nat.add(_, 1n) == 1n+m : Nat}
      N.add_one(m)

# a - 1 + 1 = a and s4 <= a - 1, for s4 < a.
law pa:
  for +s4: U32
  for +a: U32
  for +hs: {Nat.is_lt(U32.to_nat(s4), U32.to_nat(a)) == True{} : Bool}
  {Nat.add(U32.to_nat((a - 1 : U32)), 1n) == U32.to_nat(a) : Nat}

def pa(s4, a, hs):
  +na = U32.to_nat(a)
  +h0 = N.lt_pos(U32.to_nat(s4), na, hs)
  %Equal.sym(Nat, U32.to_nat((a - 1 : U32)), Nat.sub(na, U32.to_nat(1)), sub_u(a, 1, %Equal.sym(Bool, Nat.is_le(1n, na), Nat.is_lt(0n, na), N.le_succ_lt(0n, na)) : {_ == True{} : Bool}; h0)) : {Nat.add(_, 1n) == na : Nat}
  sub1_add1(na, h0)

law pb:
  for +s4: U32
  for +a: U32
  for +hs: {Nat.is_lt(U32.to_nat(s4), U32.to_nat(a)) == True{} : Bool}
  {Nat.is_le(U32.to_nat(s4), U32.to_nat((a - 1 : U32))) == True{} : Bool}

def pb(s4, a, hs):
  +na = U32.to_nat(a)
  +ns = U32.to_nat(s4)
  +p = U32.to_nat((a - 1 : U32))
  +hp = pa(s4, a, hs)
  %Equal.sym(Bool, Nat.is_le(ns, p), Nat.is_lt(ns, Nat.add(p, 1n)), Equal.trans(Bool, Nat.is_le(ns, p), Nat.is_lt(ns, 1n+p), Nat.is_lt(ns, Nat.add(p, 1n)),
    Equal.sym(Bool, Nat.is_lt(ns, 1n+p), Nat.is_le(ns, p), N.lt_succ_iff(ns, p)),
    %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, N.add_one(p)) : {Nat.is_lt(ns, 1n+p) == Nat.is_lt(ns, _) : Bool}; {==})) :
    {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(p, 1n), na, hp) : {Nat.is_lt(ns, _) == True{} : Bool}
  hs

# The pieces from s4 up to the end of the allele at a: the earlier ones
# (s4 .. a-2, a comma at a-1), then it.
law pe_ext:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s4: U32
  for +a: U32
  for +e4: U32
  for +E: LL()
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_lt(U32.to_nat(s4), U32.to_nat(a)) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hE: {PS(len, t, s4, (a - 1 : U32)) == E : LL()}
  for +hc: {List.get(&2, U32, X(len, t), U32.to_nat((a - 1 : U32))) == Some{44} : Maybe<&2, U32>}
  {PS(len, t, s4, FV(len, t, a, e4)) == LS.lapp(E, [BS(len, t, a, FV(len, t, a, e4))]) : LL()}

def pe_ext(len, t, d, s4, a, e4, E, h, hs, hae, hel, hE, hc):
  +VW = X(len, t)
  +ns = U32.to_nat(s4)
  +na = U32.to_nat(a)
  +ne = U32.to_nat(e4)
  +p = U32.to_nat((a - 1 : U32))
  +c = FV(len, t, a, e4)
  %hE : {PS(len, t, s4, c) == LS.lapp(_, [BS(len, t, a, c)]) : LL()}
  %Equal.sym(Nat, U32.to_nat(c), D.first(VW, na, ne, 44), fv_val(len, t, d, a, e4, h, hae, hel)) :
    {FD.split(D.slice(VW, ns, Nat.sub(_, ns)), 44) == LS.lapp(PS(len, t, s4, (a - 1 : U32)), [D.slice(VW, na, Nat.sub(_, na))]) : LL()}
  %pa(s4, a, hs) :
    {FD.split(D.slice(VW, ns, Nat.sub(D.first(VW, _, ne, 44), ns)), 44) == LS.lapp(PS(len, t, s4, (a - 1 : U32)), [D.slice(VW, _, Nat.sub(D.first(VW, _, ne, 44), _))]) : LL()}
  LS.ext(VW, ns, p, ne, 44, pb(s4, a, hs), hc)

law len_snoc:
  for +E: LL()
  for +q: List<&2, U32>
  {List.length(&2, List<&2, U32>, LS.lapp(E, [q])) == Nat.add(List.length(&2, List<&2, U32>, E), 1n) : Nat}

def len_snoc(E, q):
  match E:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %len_snoc(t, q) : {1n+List.length(&2, List<&2, U32>, LS.lapp(t, [q])) == 1n+_ : Nat}
      {==}

law le16:
  for +m: Nat
  for +k: Nat
  for +h: {Nat.is_le(Nat.add(m, 1n+k), 17n) == True{} : Bool}
  {Nat.is_le(m, 16n) == True{} : Bool}

def le16(m, k, h):
  N.le_trans(m, Nat.add(m, k), 16n, N.le_add_r(m, k),
    %Equal.sym(Bool, Nat.is_le(Nat.add(m, k), 16n), Nat.is_le(1n+Nat.add(m, k), 17n), {==}) : {_ == True{} : Bool};
    %N.add_succ(m, k) : {Nat.is_le(_, 17n) == True{} : Bool};
    h)

# The allele at a against the earlier ones (pieces of s4 .. a-2), for s4 < a.
law dval:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s4: U32
  for +a: U32
  for +e4: U32
  for +E: LL()
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_lt(U32.to_nat(s4), U32.to_nat(a)) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hE: {PS(len, t, s4, (a - 1 : U32)) == E : LL()}
  for +h16: {Nat.is_le(List.length(&2, List<&2, U32>, E), 16n) == True{} : Bool}
  {NF.dup(U32.is_lt(s4, a), C.BT(len, t), a, (FV(len, t, a, e4) - a : U32), s4, (a - 1 : U32)) == (C.BT(len, t), memb(BS(len, t, a, FV(len, t, a, e4)), E)) : D.Bytes & Bool}

def dval(len, t, d, s4, a, e4, E, h, hs, hae, hel, hE, h16):
  +c = FV(len, t, a, e4)
  +na = U32.to_nat(a)
  +a1 = (a - 1 : U32)
  +hr = fv_range(len, t, d, a, e4, h, hae, hel)
  +hp = pa(s4, a, hs)
  +hpl = {%hp : {Nat.is_le(U32.to_nat(a1), _) == True{} : Bool}; N.le_add_r(U32.to_nat(a1), 1n) : {Nat.is_le(U32.to_nat(a1), na) == True{} : Bool}}
  %Equal.sym(Bool, U32.is_lt(s4, a), True{}, lt_u(s4, a, hs)) :
    {NF.dup(_, C.BT(len, t), a, (c - a : U32), s4, a1) == (C.BT(len, t), memb(BS(len, t, a, c), E)) : D.Bytes & Bool}
  %hE : {NF.dup.go(16n, NF.Dp{C.BT(len, t), a, (c - a : U32), s4, a1, False{}, True{}}) == (C.BT(len, t), memb(BS(len, t, a, c), _)) : D.Bytes & Bool}
  %sub_u(c, a, cle(na, U32.to_nat(c), U32.to_nat(e4), hr)) :
    {NF.dup.go(16n, NF.Dp{C.BT(len, t), a, (c - a : U32), s4, a1, False{}, True{}}) == (C.BT(len, t), memb(D.slice(X(len, t), na, _), PS(len, t, s4, a1))) : D.Bytes & Bool}
  dgo(16n, len, t, d, a, (c - a : U32), s4, a1, h, fit_ac(a, c, e4, len, hr, hel), pb(s4, a, hs),
    N.le_trans(U32.to_nat(a1), na, U32.to_nat(len), hpl, N.le_trans(na, U32.to_nat(e4), U32.to_nat(len), hae, hel)),
    %Equal.sym(LL(), PS(len, t, s4, a1), E, hE) : {Nat.is_le(List.length(&2, List<&2, U32>, _), 16n) == True{} : Bool}; h16)

# The alts loop
# =============

law ok_lt:
  for +len: U32
  for +t: P.Tree<U32>
  for +s3: U32
  for +l3: U32
  for +a: U32
  for +e4: U32
  for +E: LL()
  for +eo: {OK3(len, t, s3, l3, a, e4, E) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(a), U32.to_nat(FV(len, t, a, e4))) == True{} : Bool}

def ok_lt(len, t, s3, l3, a, e4, E, eo):
  +c = FV(len, t, a, e4)
  +q = BS(len, t, a, c)
  +U0 = up(q)
  +LTq = U32.is_lt(a, c)
  +NR = Bool.not(D.list_eq(q, SL(len, t, s3, l3)))
  +NM = Bool.not(memb(q, E))
  lt_n(a, c, LS.and_r(U0, LTq, LS.and_l(Bool.and(U0, LTq), NR, LS.and_l(Bool.and(Bool.and(U0, LTq), NR), NM, eo))))

law fv_le_len:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  {Nat.is_le(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(len)) == True{} : Bool}

def fv_le_len(len, t, d, a, e4, h, hae, hel):
  +nc = U32.to_nat(FV(len, t, a, e4))
  N.le_trans(nc, U32.to_nat(e4), U32.to_nat(len), cre(U32.to_nat(a), nc, U32.to_nat(e4), fv_range(len, t, d, a, e4, h, hae, hel)), hel)

def AKG(+len: U32, +t: P.Tree<U32>, +s3: U32, +l3: U32, +f3: U32, +z3: U32, +a: U32, +e4: U32, +E: LL(), +L: Bool, +Fi: Bool, +G: Bool) -> Type:
  {Bool.and(okq(BS(len, t, a, FV(len, t, a, e4)), Con{SL(len, t, s3, l3), E}), spec(TS(len, t, FV(len, t, a, e4), e4), Con{SL(len, t, s3, l3), LS.lapp(E, [BS(len, t, a, FV(len, t, a, e4))])}, z3, f3, LN(len, t, z3, a, e4, L), Bool.and(Fi, U32.is_eq(headb(BS(len, t, a, FV(len, t, a, e4)), 0), f3)), GN(len, t, a, e4, G))) == True{} : Bool}

def aloop.k(+o: Bool, +b: Bool, +k: Nat, +len: U32, +t: P.Tree<U32>, +d: Nat, +s3: U32, +l3: U32, +f3: U32, +z3: U32, +s4: U32, +e4: U32, +a: U32, +E: LL(), +L: Bool, +Fi: Bool, +G: Bool,
  +eo: {OK3(len, t, s3, l3, a, e4, E) == o : Bool},
  +eb: {U32.is_lt(FV(len, t, a, e4), e4) == b : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool},
  +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool},
  +hres: {NF.alts.go(k, NF.As{C.BT(len, t), AL(s3, l3, f3, z3, s4, e4), (FV(len, t, a, e4) + 1 : U32), o, LN(len, t, z3, a, e4, L), FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G), Bool.and(o, b)}) == (C.BT(len, t), True{}) : D.Bytes & Bool},
  ih: {Bool.and(o, b) == True{} : Bool} -> {spec(PS(len, t, (FV(len, t, a, e4) + 1 : U32), e4), Con{SL(len, t, s3, l3), LS.lapp(E, [BS(len, t, a, FV(len, t, a, e4))])}, z3, f3, LN(len, t, z3, a, e4, L), FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G)) == True{} : Bool}) ->
  AKG(len, t, s3, l3, f3, z3, a, e4, E, L, Fi, G):
  match o b k:
    case False{} _ 0n:
      Empty.absurd(AKG(len, t, s3, l3, f3, z3, a, e4, E, L, Fi, G), pft(C.BT(len, t), C.BT(len, t), hres))
    case False{} _ 1n+j:
      Empty.absurd(AKG(len, t, s3, l3, f3, z3, a, e4, E, L, Fi, G), pft(C.BT(len, t), C.BT(len, t), hres))
    case True{} False{} 0n:
      Empty.absurd(AKG(len, t, s3, l3, f3, z3, a, e4, E, L, Fi, G), pft(C.BT(len, t), C.BT(len, t), hres))
    case True{} True{} _:
      +c = FV(len, t, a, e4)
      +Q1 = BS(len, t, a, c)
      +RR = SL(len, t, s3, l3)
      +E2 = LS.lapp(E, [Q1])
      +hlt = lt_n(c, e4, eb)
      %Equal.sym(Bool, okq(Q1, Con{RR, E}), True{}, okq_t(len, t, d, s3, l3, a, e4, E, h, hae, hel, eo)) :
        {Bool.and(_, spec(TS(len, t, c, e4), Con{RR, E2}, z3, f3, LN(len, t, z3, a, e4, L), Bool.and(Fi, U32.is_eq(headb(Q1, 0), f3)), GN(len, t, a, e4, G))) == True{} : Bool}
      %Equal.sym(U32, headb(Q1, 0), C.AT(len, t, a), hd_at(len, t, d, a, c, h, ok_lt(len, t, s3, l3, a, e4, E, eo), fv_le_len(len, t, d, a, e4, h, hae, hel))) :
        {spec(TS(len, t, c, e4), Con{RR, E2}, z3, f3, LN(len, t, z3, a, e4, L), Bool.and(Fi, U32.is_eq(_, f3)), GN(len, t, a, e4, G)) == True{} : Bool}
      %Equal.sym(LL(), TS(len, t, c, e4), PS(len, t, (c + 1 : U32), e4), ts_next(len, t, d, c, e4, h, hel, hlt, fv_hit(len, t, d, a, e4, h, hae, hel, hlt))) :
        {spec(_, Con{RR, E2}, z3, f3, LN(len, t, z3, a, e4, L), FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G)) == True{} : Bool}
      ih({==})
    case True{} False{} 1n+j:
      +c = FV(len, t, a, e4)
      +Q1 = BS(len, t, a, c)
      +RR = SL(len, t, s3, l3)
      +E2 = LS.lapp(E, [Q1])
      %Equal.sym(Bool, okq(Q1, Con{RR, E}), True{}, okq_t(len, t, d, s3, l3, a, e4, E, h, hae, hel, eo)) :
        {Bool.and(_, spec(TS(len, t, c, e4), Con{RR, E2}, z3, f3, LN(len, t, z3, a, e4, L), Bool.and(Fi, U32.is_eq(headb(Q1, 0), f3)), GN(len, t, a, e4, G))) == True{} : Bool}
      %Equal.sym(U32, headb(Q1, 0), C.AT(len, t, a), hd_at(len, t, d, a, c, h, ok_lt(len, t, s3, l3, a, e4, E, eo), fv_le_len(len, t, d, a, e4, h, hae, hel))) :
        {spec(TS(len, t, c, e4), Con{RR, E2}, z3, f3, LN(len, t, z3, a, e4, L), Bool.and(Fi, U32.is_eq(_, f3)), GN(len, t, a, e4, G)) == True{} : Bool}
      %Equal.sym(LL(), TS(len, t, c, e4), Nil{}, ts_last(len, t, c, e4, fv_end(len, t, d, a, e4, h, hae, hel, eb))) :
        {spec(_, Con{RR, E2}, z3, f3, LN(len, t, z3, a, e4, L), FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G)) == True{} : Bool}
      psnd(C.BT(len, t), C.BT(len, t), Bool.and(Bool.not(LN(len, t, z3, a, e4, L)), Bool.not(Bool.and(FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G)))), hres)

law nx_lt:
  for +len: U32
  for +t: P.Tree<U32>
  for +s3: U32
  for +l3: U32
  for +a: U32
  for +e4: U32
  for +E: LL()
  for +hob: {Bool.and(OK3(len, t, s3, l3, a, e4, E), U32.is_lt(FV(len, t, a, e4), e4)) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4)) == True{} : Bool}

def nx_lt(len, t, s3, l3, a, e4, E, hob):
  lt_n(FV(len, t, a, e4), e4, LS.and_r(OK3(len, t, s3, l3, a, e4, E), U32.is_lt(FV(len, t, a, e4), e4), hob))

law nx_inc:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4)) == True{} : Bool}
  {U32.to_nat((FV(len, t, a, e4) + 1 : U32)) == Nat.add(U32.to_nat(FV(len, t, a, e4)), 1n) : Nat}

def nx_inc(len, t, d, a, e4, h, hel, hlt):
  +c = FV(len, t, a, e4)
  inc_len(len, t, d, c, h, N.lt_le_trans(U32.to_nat(c), U32.to_nat(e4), U32.to_nat(len), hlt, hel))

law nx_sa:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s4: U32
  for +a: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hsa: {Nat.is_le(U32.to_nat(s4), U32.to_nat(a)) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4)) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(s4), U32.to_nat((FV(len, t, a, e4) + 1 : U32))) == True{} : Bool}

def nx_sa(len, t, d, s4, a, e4, h, hsa, hae, hel, hlt):
  +c = FV(len, t, a, e4)
  +nc = U32.to_nat(c)
  +ns = U32.to_nat(s4)
  %Equal.sym(Nat, U32.to_nat((c + 1 : U32)), Nat.add(nc, 1n), nx_inc(len, t, d, a, e4, h, hel, hlt)) : {Nat.is_lt(ns, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(nc, 1n), 1n+nc, N.add_one(nc)) : {Nat.is_lt(ns, _) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(ns, 1n+nc), Nat.is_le(ns, nc), N.lt_succ_iff(ns, nc)) : {_ == True{} : Bool}
  N.le_trans(ns, U32.to_nat(a), nc, hsa, cle(U32.to_nat(a), nc, U32.to_nat(e4), fv_range(len, t, d, a, e4, h, hae, hel)))

law nx_ae:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4)) == True{} : Bool}
  {Nat.is_le(U32.to_nat((FV(len, t, a, e4) + 1 : U32)), U32.to_nat(e4)) == True{} : Bool}

def nx_ae(len, t, d, a, e4, h, hel, hlt):
  %Equal.sym(Nat, U32.to_nat((FV(len, t, a, e4) + 1 : U32)), Nat.add(U32.to_nat(FV(len, t, a, e4)), 1n), nx_inc(len, t, d, a, e4, h, hel, hlt)) : {Nat.is_le(_, U32.to_nat(e4)) == True{} : Bool}
  C.succ_le(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4), hlt)

law nx_dec:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4)) == True{} : Bool}
  {U32.to_nat(((FV(len, t, a, e4) + 1 : U32) - 1 : U32)) == U32.to_nat(FV(len, t, a, e4)) : Nat}

def nx_dec(len, t, d, a, e4, h, hel, hlt):
  +c = FV(len, t, a, e4)
  dec_inc(len, t, d, c, h, N.lt_le_trans(U32.to_nat(c), U32.to_nat(e4), U32.to_nat(len), hlt, hel))

law nx_E:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s4: U32
  for +a: U32
  for +e4: U32
  for +E: LL()
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4)) == True{} : Bool}
  for +hEn: {PS(len, t, s4, FV(len, t, a, e4)) == LS.lapp(E, [BS(len, t, a, FV(len, t, a, e4))]) : LL()}
  {PS(len, t, s4, ((FV(len, t, a, e4) + 1 : U32) - 1 : U32)) == LS.lapp(E, [BS(len, t, a, FV(len, t, a, e4))]) : LL()}

def nx_E(len, t, d, s4, a, e4, E, h, hel, hlt, hEn):
  +c = FV(len, t, a, e4)
  +ns = U32.to_nat(s4)
  %Equal.sym(Nat, U32.to_nat(((c + 1 : U32) - 1 : U32)), U32.to_nat(c), nx_dec(len, t, d, a, e4, h, hel, hlt)) :
    {FD.split(D.slice(X(len, t), ns, Nat.sub(_, ns)), 44) == LS.lapp(E, [BS(len, t, a, c)]) : LL()}
  hEn

law nx_c:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +a: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(FV(len, t, a, e4)), U32.to_nat(e4)) == True{} : Bool}
  {List.get(&2, U32, X(len, t), U32.to_nat(((FV(len, t, a, e4) + 1 : U32) - 1 : U32))) == Some{44} : Maybe<&2, U32>}

def nx_c(len, t, d, a, e4, h, hae, hel, hlt):
  +c = FV(len, t, a, e4)
  %Equal.sym(Nat, U32.to_nat(((c + 1 : U32) - 1 : U32)), U32.to_nat(c), nx_dec(len, t, d, a, e4, h, hel, hlt)) :
    {List.get(&2, U32, X(len, t), _) == Some{44} : Maybe<&2, U32>}
  fv_hit(len, t, d, a, e4, h, hae, hel, hlt)

law nx_f:
  for +E: LL()
  for +q: List<&2, U32>
  for +k: Nat
  for +hf: {Nat.is_le(Nat.add(List.length(&2, List<&2, U32>, E), 1n+k), 17n) == True{} : Bool}
  {Nat.is_le(Nat.add(List.length(&2, List<&2, U32>, LS.lapp(E, [q])), k), 17n) == True{} : Bool}

def nx_f(E, q, k, hf):
  +m = List.length(&2, List<&2, U32>, E)
  %Equal.sym(Nat, List.length(&2, List<&2, U32>, LS.lapp(E, [q])), Nat.add(m, 1n), len_snoc(E, q)) : {Nat.is_le(Nat.add(_, k), 17n) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(m, 1n), k), Nat.add(m, Nat.add(1n, k)), N.add_assoc(m, 1n, k)) : {Nat.is_le(_, 17n) == True{} : Bool}
  hf

def SPG(+len: U32, +t: P.Tree<U32>, +s3: U32, +l3: U32, +f3: U32, +z3: U32, +a: U32, +e4: U32, +E: LL(), +L: Bool, +Fi: Bool, +G: Bool) -> Type:
  {spec(PS(len, t, a, e4), Con{SL(len, t, s3, l3), E}, z3, f3, L, Fi, G) == True{} : Bool}

def DUPH(+len: U32, +t: P.Tree<U32>, +s4: U32, +a: U32, +e4: U32, +E: LL()) -> Type:
  {NF.dup(U32.is_lt(s4, a), C.BT(len, t), a, (FV(len, t, a, e4) - a : U32), s4, (a - 1 : U32)) == (C.BT(len, t), memb(BS(len, t, a, FV(len, t, a, e4)), E)) : D.Bytes & Bool}

# The ALT alleles from a on pass the loop: they pass spec. E: the earlier
# alleles (from s4); hEn: with the allele at a, they are the pieces of s4
# .. its end; hDf: the dup test at a answers whether it is one of E.
def aloop(+n: Nat, +len: U32, +t: P.Tree<U32>, +d: Nat, +s3: U32, +l3: U32, +f3: U32, +z3: U32, +s4: U32, +e4: U32, +a: U32, +ok: Bool, +L: Bool, +Fi: Bool, +G: Bool, +E: LL(),
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(s3), U32.to_nat(l3)), U32.to_nat(len)) == True{} : Bool},
  +hsa: {Nat.is_le(U32.to_nat(s4), U32.to_nat(a)) == True{} : Bool},
  +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e4)) == True{} : Bool},
  +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool},
  +hEn: {PS(len, t, s4, FV(len, t, a, e4)) == LS.lapp(E, [BS(len, t, a, FV(len, t, a, e4))]) : LL()},
  +hf: {Nat.is_le(Nat.add(List.length(&2, List<&2, U32>, E), n), 17n) == True{} : Bool},
  +hres: {NF.alts.go(n, NF.As{C.BT(len, t), AL(s3, l3, f3, z3, s4, e4), a, ok, L, Fi, G, True{}}) == (C.BT(len, t), True{}) : D.Bytes & Bool},
  hDf: {Nat.is_le(List.length(&2, List<&2, U32>, E), 16n) == True{} : Bool} -> DUPH(len, t, s4, a, e4, E)) ->
  SPG(len, t, s3, l3, f3, z3, a, e4, E, L, Fi, G):
  match n:
    case 0n:
      Empty.absurd(SPG(len, t, s3, l3, f3, z3, a, e4, E, L, Fi, G), pft(C.BT(len, t), C.BT(len, t), hres))
    case 1n+k:
      +c = FV(len, t, a, e4)
      +Q1 = BS(len, t, a, c)
      +RR = SL(len, t, s3, l3)
      +E2 = LS.lapp(E, [Q1])
      +o = OK3(len, t, s3, l3, a, e4, E)
      +hr = fv_range(len, t, d, a, e4, h, hae, hel)
      +hres2 = Equal.trans(D.Bytes & Bool, ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G), NF.alts.go(1n+k, NF.As{C.BT(len, t), AL(s3, l3, f3, z3, s4, e4), a, ok, L, Fi, G, True{}}), (C.BT(len, t), True{}),
        Equal.sym(D.Bytes & Bool, NF.alts.go(1n+k, NF.As{C.BT(len, t), AL(s3, l3, f3, z3, s4, e4), a, ok, L, Fi, G, True{}}), ANX(k, len, t, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G),
          astep(k, len, t, d, s3, l3, f3, z3, s4, e4, a, ok, L, Fi, G, E, h, h3, hae, hel, hDf(le16(List.length(&2, List<&2, U32>, E), k, hf)))),
        hres)
      %Equal.sym(LL(), PS(len, t, a, e4), Con{Q1, TS(len, t, c, e4)}, ps_first(len, t, d, a, e4, h, hae, hel)) :
        {spec(_, Con{RR, E}, z3, f3, L, Fi, G) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(2n, List.length(&2, U32, Q1)), U32.is_le(2, (c - a : U32)), ge2(len, t, d, a, c, h, cle(U32.to_nat(a), U32.to_nat(c), U32.to_nat(e4), hr), fv_le_len(len, t, d, a, e4, h, hae, hel))) :
        {Bool.and(okq(Q1, Con{RR, E}), spec(TS(len, t, c, e4), Con{RR, E2}, z3, f3, Bool.and(L, U32.is_eq(lastb(Q1, 0), z3)), Bool.and(Fi, U32.is_eq(headb(Q1, 0), f3)), Bool.and(G, _))) == True{} : Bool}
      aloop.k(o, U32.is_lt(c, e4), k, len, t, d, s3, l3, f3, z3, s4, e4, a, E, L, Fi, G, {==}, {==}, h, hae, hel, hres2,
        +hob => aloop(k, len, t, d, s3, l3, f3, z3, s4, e4, (c + 1 : U32), o, LN(len, t, z3, a, e4, L), FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G), E2, h, h3,
          N.lt_to_le(U32.to_nat(s4), U32.to_nat((c + 1 : U32)), nx_sa(len, t, d, s4, a, e4, h, hsa, hae, hel, nx_lt(len, t, s3, l3, a, e4, E, hob))),
          nx_ae(len, t, d, a, e4, h, hel, nx_lt(len, t, s3, l3, a, e4, E, hob)),
          hel,
          pe_ext(len, t, d, s4, (c + 1 : U32), e4, E2, h, nx_sa(len, t, d, s4, a, e4, h, hsa, hae, hel, nx_lt(len, t, s3, l3, a, e4, E, hob)),
            nx_ae(len, t, d, a, e4, h, hel, nx_lt(len, t, s3, l3, a, e4, E, hob)), hel,
            nx_E(len, t, d, s4, a, e4, E, h, hel, nx_lt(len, t, s3, l3, a, e4, E, hob), hEn),
            nx_c(len, t, d, a, e4, h, hae, hel, nx_lt(len, t, s3, l3, a, e4, E, hob))),
          nx_f(E, Q1, k, hf),
          %hob : {NF.alts.go(k, NF.As{C.BT(len, t), AL(s3, l3, f3, z3, s4, e4), (c + 1 : U32), o, LN(len, t, z3, a, e4, L), FN(len, t, f3, a, e4, Fi), GN(len, t, a, e4, G), _}) == (C.BT(len, t), True{}) : D.Bytes & Bool};
          hres2,
          +h16 => dval(len, t, d, s4, (c + 1 : U32), e4, E2, h, nx_sa(len, t, d, s4, a, e4, h, hsa, hae, hel, nx_lt(len, t, s3, l3, a, e4, E, hob)),
            nx_ae(len, t, d, a, e4, h, hel, nx_lt(len, t, s3, l3, a, e4, E, hob)), hel,
            nx_E(len, t, d, s4, a, e4, E, h, hel, nx_lt(len, t, s3, l3, a, e4, E, hob), hEn), h16)))

# The whole test
# ==============

law lt_irr_u:
  for +a: U32
  {U32.is_lt(a, a) == False{} : Bool}

def lt_irr_u(a):
  %Equal.sym(Bool, U32.is_lt(a, a), Nat.is_lt(U32.to_nat(a), U32.to_nat(a)), U.is_lt_to_nat(a, a)) : {_ == False{} : Bool}
  N.lt_irrefl(U32.to_nat(a))

law en0:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s4: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +h4: {Nat.is_le(U32.to_nat(s4), U32.to_nat(e4)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  {PS(len, t, s4, FV(len, t, s4, e4)) == LS.lapp(Nil{}, [BS(len, t, s4, FV(len, t, s4, e4))]) : LL()}

def en0(len, t, d, s4, e4, h, h4, hel):
  +VW = X(len, t)
  +ns = U32.to_nat(s4)
  +ne = U32.to_nat(e4)
  %Equal.sym(Nat, U32.to_nat(FV(len, t, s4, e4)), D.first(VW, ns, ne, 44), fv_val(len, t, d, s4, e4, h, h4, hel)) :
    {FD.split(D.slice(VW, ns, Nat.sub(_, ns)), 44) == [D.slice(VW, ns, Nat.sub(_, ns))] : LL()}
  LS.one(VW, ns, ne, 44)

law dup0:
  for +len: U32
  for +t: P.Tree<U32>
  for +s4: U32
  for +e4: U32
  DUPH(len, t, s4, s4, e4, Nil{})

def dup0(len, t, s4, e4):
  %Equal.sym(Bool, U32.is_lt(s4, s4), False{}, lt_irr_u(s4)) :
    {NF.dup(_, C.BT(len, t), s4, (FV(len, t, s4, e4) - s4 : U32), s4, (s4 - 1 : U32)) == (C.BT(len, t), False{}) : D.Bytes & Bool}
  {==}

def GO(+len: U32, +t: P.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32) -> Bool:
  Bool.and(Bool.and(up(BS(len, t, s3, e3)), U32.is_lt(s3, e3)), U32.is_lt(s4, e4))

def L3(+s3: U32, +e3: U32) -> U32:
  (e3 - s3 : U32)

def Z3(+len: U32, +t: P.Tree<U32>, +s3: U32, +e3: U32) -> U32:
  lastb(BS(len, t, s3, e3), 0)

def AL0(+len: U32, +t: P.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32) -> NF.Al:
  AL(s3, L3(s3, e3), C.AT(len, t, s3), Z3(len, t, s3, e3), s4, e4)

law top_eq:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s3: U32
  for +e3: U32
  for +s4: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +h3: {Nat.is_le(U32.to_nat(s3), U32.to_nat(e3)) == True{} : Bool}
  for +he3: {Nat.is_le(U32.to_nat(e3), U32.to_nat(len)) == True{} : Bool}
  {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, GO(len, t, s3, e3, s4, e4), True{}, True{}, U32.is_le(2, L3(s3, e3)), GO(len, t, s3, e3, s4, e4)}) : D.Bytes & Bool}

def top_eq(len, t, d, s3, e3, s4, e4, h, h3, he3):
  +R0 = BS(len, t, s3, e3)
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), s3), (C.BT(len, t), C.AT(len, t, s3)), C.at_pair_t(len, t, s3)) :
    {NF.alleles.f(s3, e3, s4, e4, _) == NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, GO(len, t, s3, e3, s4, e4), True{}, True{}, U32.is_le(2, L3(s3, e3)), GO(len, t, s3, e3, s4, e4)}) : D.Bytes & Bool}
  %Equal.sym(NF.Bv, NF.bases(C.BT(len, t), s3, e3), NF.Bv{C.BT(len, t), up(R0), lastb(R0, 0)}, bases_t(len, t, d, s3, e3, h, h3, he3)) :
    {NF.alleles.k(s3, e3, s4, e4, C.AT(len, t, s3), _) == NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, GO(len, t, s3, e3, s4, e4), True{}, True{}, U32.is_le(2, L3(s3, e3)), GO(len, t, s3, e3, s4, e4)}) : D.Bytes & Bool}
  {==}

def go.k(+g: Bool, +len: U32, +t: P.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32,
  +hres: {NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, g, True{}, True{}, U32.is_le(2, L3(s3, e3)), g}) == (C.BT(len, t), True{}) : D.Bytes & Bool}) ->
  {g == True{} : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, pft(C.BT(len, t), C.BT(len, t), hres))

law hres0:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s3: U32
  for +e3: U32
  for +s4: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +h3: {Nat.is_le(U32.to_nat(s3), U32.to_nat(e3)) == True{} : Bool}
  for +he3: {Nat.is_le(U32.to_nat(e3), U32.to_nat(len)) == True{} : Bool}
  for +hp: {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}
  {NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, GO(len, t, s3, e3, s4, e4), True{}, True{}, U32.is_le(2, L3(s3, e3)), GO(len, t, s3, e3, s4, e4)}) == (C.BT(len, t), True{}) : D.Bytes & Bool}

def hres0(len, t, d, s3, e3, s4, e4, h, h3, he3, hp):
  Equal.trans(D.Bytes & Bool, NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, GO(len, t, s3, e3, s4, e4), True{}, True{}, U32.is_le(2, L3(s3, e3)), GO(len, t, s3, e3, s4, e4)}),
    NF.alleles(C.BT(len, t), s3, e3, s4, e4), (C.BT(len, t), True{}),
    Equal.sym(D.Bytes & Bool, NF.alleles(C.BT(len, t), s3, e3, s4, e4), NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, GO(len, t, s3, e3, s4, e4), True{}, True{}, U32.is_le(2, L3(s3, e3)), GO(len, t, s3, e3, s4, e4)}),
      top_eq(len, t, d, s3, e3, s4, e4, h, h3, he3)),
    hp)

# REF is all bases, REF and ALT are not empty.
law go_true:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s3: U32
  for +e3: U32
  for +s4: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +h3: {Nat.is_le(U32.to_nat(s3), U32.to_nat(e3)) == True{} : Bool}
  for +he3: {Nat.is_le(U32.to_nat(e3), U32.to_nat(len)) == True{} : Bool}
  for +hp: {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}
  {GO(len, t, s3, e3, s4, e4) == True{} : Bool}

def go_true(len, t, d, s3, e3, s4, e4, h, h3, he3, hp):
  go.k(GO(len, t, s3, e3, s4, e4), len, t, s3, e3, s4, e4, hres0(len, t, d, s3, e3, s4, e4, h, h3, he3, hp))

# The ALT alleles pass spec, with REF (s3 .. e3-1) the only earlier allele.
law alleles_spec:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s3: U32
  for +e3: U32
  for +s4: U32
  for +e4: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +h3: {Nat.is_le(U32.to_nat(s3), U32.to_nat(e3)) == True{} : Bool}
  for +h4: {Nat.is_le(U32.to_nat(s4), U32.to_nat(e4)) == True{} : Bool}
  for +he3: {Nat.is_le(U32.to_nat(e3), U32.to_nat(len)) == True{} : Bool}
  for +hel: {Nat.is_le(U32.to_nat(e4), U32.to_nat(len)) == True{} : Bool}
  for +hp: {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}
  {spec(PS(len, t, s4, e4), [BS(len, t, s3, e3)], Z3(len, t, s3, e3), C.AT(len, t, s3), True{}, True{}, U32.is_le(2, L3(s3, e3))) == True{} : Bool}

def alleles_spec(len, t, d, s3, e3, s4, e4, h, h3, h4, he3, hel, hp):
  +ns3 = U32.to_nat(s3)
  +ne3 = U32.to_nat(e3)
  +l3 = L3(s3, e3)
  +eg = go_true(len, t, d, s3, e3, s4, e4, h, h3, he3, hp)
  %sub_u(e3, s3, h3) :
    {spec(PS(len, t, s4, e4), [D.slice(X(len, t), ns3, _)], Z3(len, t, s3, e3), C.AT(len, t, s3), True{}, True{}, U32.is_le(2, l3)) == True{} : Bool}
  aloop(17n, len, t, d, s3, l3, C.AT(len, t, s3), Z3(len, t, s3, e3), s4, e4, s4, True{}, True{}, True{}, U32.is_le(2, l3), Nil{}, h,
    %Equal.sym(Nat, U32.to_nat(l3), Nat.sub(ne3, ns3), sub_u(e3, s3, h3)) : {Nat.is_le(Nat.add(ns3, _), U32.to_nat(len)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(ns3, Nat.sub(ne3, ns3)), ne3, N.le_sub_add(ns3, ne3, h3)) : {Nat.is_le(_, U32.to_nat(len)) == True{} : Bool};
    he3,
    N.le_refl(U32.to_nat(s4)), h4, hel, en0(len, t, d, s4, e4, h, h4, hel), {==},
    %eg : {NF.alts.go(17n, NF.As{C.BT(len, t), AL0(len, t, s3, e3, s4, e4), s4, _, True{}, True{}, U32.is_le(2, l3), _}) == (C.BT(len, t), True{}) : D.Bytes & Bool};
    hres0(len, t, d, s3, e3, s4, e4, h, h3, he3, hp),
    x => dup0(len, t, s4, e4))
