import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as AL
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_scan.bend as SC
import ./proof_s_read.bend as RD
import ./proof_s_cut.bend as K
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_same.bend as S
import lawful-bytes@0.1.1.0/proof_seq.bend as Q
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The byte splitter's test that no two ALTs are equal up to case
# (norm_split.bend's same_ci, member_ci, distinct) is B.Alts.distinct of the
# ALTs' text. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def X(+len: U32, +t: AT.Tree<U32>) -> L32():
  D.view(C.BT(len, t))

# ---------------------------------------------------------------------------
# Upper case on bytes
# ---------------------------------------------------------------------------

def UPL(xs: L32()) -> L32():
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{NS.up(x), UPL(t)}

law sub0:
  for +x: U32
  {U32.sub(x, 0) == x : U32}

def sub0(x):
  U.to_nat_inj(U32.sub(x, 0), x, Equal.trans(Nat, n(U32.sub(x, 0)), Nat.sub(n(x), 0n), n(x), U.to_nat_sub_le(x, 0, Equal.trans(Bool, U32.is_le(0, x), Nat.is_le(n(0), n(x)), True{}, U.is_le_to_nat(0, x), N.le_zero_l(n(x)))), N.sub_zero(n(x))))

def up_chr.k(+b: Bool, +x: U32) -> {Chr{U32.sub(x, U32.mul(Bool.to_u32(b), 32))} == Chr{Bool.pick(U32, b, (x - 32 : U32), x)} : Char}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(U32, U32.sub(x, 0), x, sub0(x)) : {Chr{_} == Chr{x} : Char}
      {==}

law up_chr:
  for +x: U32
  {Char.to_upper(Chr{x}) == Chr{NS.up(x)} : Char}

def up_chr(x):
  up_chr.k(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122)), x)

law upper_chars:
  for +xs: L32()
  {String.to_upper(NR.chars(xs)) == NR.chars(UPL(xs)) : String}

def upper_chars(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Char, Char.to_upper(Chr{x}), Chr{NS.up(x)}, up_chr(x)) : {SCon{_, String.to_upper(NR.chars(r))} == SCon{Chr{NS.up(x)}, NR.chars(UPL(r))} : String}
      %Equal.sym(String, String.to_upper(NR.chars(r)), NR.chars(UPL(r)), upper_chars(r)) : {SCon{Chr{NS.up(x)}, _} == SCon{Chr{NS.up(x)}, NR.chars(UPL(r))} : String}
      {==}

law upl_len:
  for +xs: L32()
  {List.length(&2, U32, UPL(xs)) == List.length(&2, U32, xs) : Nat}

def upl_len(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Nat, List.length(&2, U32, UPL(r)), List.length(&2, U32, r), upl_len(r)) : {1n+_ == 1n+List.length(&2, U32, r) : Nat}
      {==}

# ---------------------------------------------------------------------------
# same_ci
# ---------------------------------------------------------------------------

def SLN(+len: U32, +t: AT.Tree<U32>, +i: U32, +k: Nat) -> L32():
  D.slice(X(len, t), n(i), k)

def SCR(+len: U32, +t: AT.Tree<U32>, +i: U32, +j: U32, +k: Nat, -r: D.Bytes & Bool) -> Type:
  {r == (C.BT(len, t), D.list_eq(UPL(SLN(len, t, i, k)), UPL(SLN(len, t, j, k)))) : D.Bytes & Bool}

def sc_false(+q: Nat, +len: U32, +t: AT.Tree<U32>, +i: U32, +j: U32, +left: U32) ->
  {NS.same_ci.loop(q, NS.Sc{C.BT(len, t), i, j, left, False{}}) == NS.Sc{C.BT(len, t), i, j, left, False{}} : NS.Sc}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

law sc_zero:
  for +q: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +i: U32
  for +j: U32
  for +left: U32
  for +hz: {U32.is_zero(left) == True{} : Bool}
  {NS.same_ci.loop(q, NS.Sc{C.BT(len, t), i, j, left, True{}}) == NS.Sc{C.BT(len, t), i, j, left, True{}} : NS.Sc}

def sc_zero(q, len, t, i, j, left, hz):
  match q:
    case 0n:
      {==}
    case 1n+r:
      %Equal.sym(Bool, U32.is_zero(left), True{}, hz) : {NS.same_ci.loop(r, NS.same_ci.go(_, C.BT(len, t), i, j, left)) == NS.Sc{C.BT(len, t), i, j, left, True{}} : NS.Sc}
      sc_zero(r, len, t, i, j, left, hz)

def get_at(+len: U32, +t: AT.Tree<U32>, +d: Nat, +i: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hi: {Nat.is_lt(n(i), n(len)) == True{} : Bool}) ->
  {List.get(&2, U32, X(len, t), n(i)) == Some{C.AT(len, t, i)} : Maybe<&2, U32>}:
  Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, i)}, List.get(&2, U32, X(len, t), n(i)),
    C.at_view_t(len, t, d, i, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hi))

# i + 1 + k <= len: the slice of 1 + k from i is byte i and k more.
def scons(+len: U32, +t: AT.Tree<U32>, +d: Nat, +i: U32, +k: Nat,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hi: {Nat.is_le(Nat.add(n(i), 1n+k), n(len)) == True{} : Bool}) ->
  {SLN(len, t, i, 1n+k) == C.AT(len, t, i) <> SLN(len, t, (i + 1 : U32), k) : L32()}:
  +hlt = N.lt_le_trans(n(i), Nat.add(n(i), 1n+k), n(len), {%Equal.sym(Nat, Nat.add(n(i), 1n+k), 1n+Nat.add(n(i), k), N.add_succ(n(i), k)) : {Nat.is_lt(n(i), _) == True{} : Bool}; %N.le_succ_lt(n(i), 1n+Nat.add(n(i), k)) : {_ == True{} : Bool}; N.le_add_r(n(i), k) : {Nat.is_lt(n(i), Nat.add(n(i), 1n+k)) == True{} : Bool}}, hi)
  %Equal.sym(Nat, n((i + 1 : U32)), Nat.add(n(i), 1n), AL.inc_len(len, t, d, i, h, hlt)) : {SLN(len, t, i, 1n+k) == C.AT(len, t, i) <> D.slice(X(len, t), _, k) : L32()}
  S.slice_cons(X(len, t), n(i), k, C.AT(len, t, i), get_at(len, t, d, i, h, hlt))

def le_add1(+i: Nat, +k: Nat, +L: Nat, +h: {Nat.is_le(Nat.add(i, 1n+k), L) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(i, 1n), k), L) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(i, 1n), k), Nat.add(i, Nat.add(1n, k)), N.add_assoc(i, 1n, k)) : {Nat.is_le(_, L) == True{} : Bool}
  h

def lt_of_add(+i: Nat, +k: Nat, +L: Nat, +h: {Nat.is_le(Nat.add(i, 1n+k), L) == True{} : Bool}) -> {Nat.is_lt(i, L) == True{} : Bool}:
  +h1 = {%Equal.sym(Nat, Nat.add(i, 1n+k), 1n+Nat.add(i, k), N.add_succ(i, k)) : {Nat.is_lt(i, _) == True{} : Bool};
    %N.le_succ_lt(i, 1n+Nat.add(i, k)) : {_ == True{} : Bool};
    N.le_add_r(i, k) : {Nat.is_lt(i, Nat.add(i, 1n+k)) == True{} : Bool}}
  N.lt_le_trans(i, Nat.add(i, 1n+k), L, h1, h)

# The next state's bound: (i + 1) + (left - 1) = i + 1 + k.
def ij1(+len: U32, +t: AT.Tree<U32>, +d: Nat, +i: U32, +left: U32, +k: Nat,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hi2: {Nat.is_le(Nat.add(n(i), 1n+k), n(len)) == True{} : Bool},
  +hk: {n((left - 1 : U32)) == k : Nat}) ->
  {Nat.add(n((i + 1 : U32)), n((left - 1 : U32))) == Nat.add(Nat.add(n(i), 1n), k) : Nat}:
  %Equal.sym(Nat, n((i + 1 : U32)), Nat.add(n(i), 1n), AL.inc_len(len, t, d, i, h, lt_of_add(n(i), k, n(len), hi2))) : {Nat.add(_, n((left - 1 : U32))) == Nat.add(Nat.add(n(i), 1n), k) : Nat}
  %Equal.sym(Nat, n((left - 1 : U32)), k, hk) : {Nat.add(Nat.add(n(i), 1n), _) == Nat.add(Nat.add(n(i), 1n), k) : Nat}
  {==}

def sc.c(+c: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +i: U32, +j: U32, +left: U32, +k: Nat,
  +hk: {n((left - 1 : U32)) == k : Nat},
  +hc: {U32.is_eq(NS.up(C.AT(len, t, i)), NS.up(C.AT(len, t, j))) == c : Bool},
  ih: SCR(len, t, (i + 1 : U32), (j + 1 : U32), n((left - 1 : U32)), NS.same_ci.fin(NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), True{}})))) ->
  {NS.same_ci.fin(NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), c})) ==
    (C.BT(len, t), Bool.and(c, D.list_eq(UPL(SLN(len, t, (i + 1 : U32), k)), UPL(SLN(len, t, (j + 1 : U32), k))))) : D.Bytes & Bool}:
  match c:
    case True{}:
      %hk : SCR(len, t, (i + 1 : U32), (j + 1 : U32), _, NS.same_ci.fin(NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), True{}})))
      ih
    case False{}:
      %Equal.sym(NS.Sc, NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), False{}}), NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), False{}},
        sc_false(q, len, t, (i + 1 : U32), (j + 1 : U32), (left - 1 : U32))) :
        {NS.same_ci.fin(_) == (C.BT(len, t), Bool.and(False{}, D.list_eq(UPL(SLN(len, t, (i + 1 : U32), k)), UPL(SLN(len, t, (j + 1 : U32), k))))) : D.Bytes & Bool}
      {==}

def sc.z(+z0: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +i: U32, +j: U32, +left: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hi: {Nat.is_le(Nat.add(n(i), n(left)), n(len)) == True{} : Bool},
  +hj: {Nat.is_le(Nat.add(n(j), n(left)), n(len)) == True{} : Bool},
  +hm: {Nat.is_lt(n(left), 1n+q) == True{} : Bool},
  +hz: {U32.is_zero(left) == z0 : Bool},
  ih: {Nat.is_le(Nat.add(n((i + 1 : U32)), n((left - 1 : U32))), n(len)) == True{} : Bool} -> {Nat.is_le(Nat.add(n((j + 1 : U32)), n((left - 1 : U32))), n(len)) == True{} : Bool} ->
    {Nat.is_lt(n((left - 1 : U32)), q) == True{} : Bool} ->
    SCR(len, t, (i + 1 : U32), (j + 1 : U32), n((left - 1 : U32)), NS.same_ci.fin(NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), True{}})))) ->
  SCR(len, t, i, j, n(left), NS.same_ci.fin(NS.same_ci.loop(q, NS.same_ci.go(z0, C.BT(len, t), i, j, left)))):
  match z0:
    case True{}:
      +e0 = N.eq_sound(n(left), 0n, Equal.trans(Bool, Nat.is_eq(n(left), 0n), U32.is_zero(left), True{}, Equal.sym(Bool, U32.is_zero(left), Nat.is_eq(n(left), 0n), U.is_zero_to_nat(left)), hz))
      %Equal.sym(NS.Sc, NS.same_ci.loop(q, NS.Sc{C.BT(len, t), i, j, left, True{}}), NS.Sc{C.BT(len, t), i, j, left, True{}}, sc_zero(q, len, t, i, j, left, hz)) :
        SCR(len, t, i, j, n(left), NS.same_ci.fin(_))
      %Equal.sym(Nat, n(left), 0n, e0) : SCR(len, t, i, j, _, (C.BT(len, t), True{}))
      %Equal.sym(L32(), List.take(&2, U32, List.drop(&2, U32, X(len, t), n(i)), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, X(len, t), n(i)))) :
        {(C.BT(len, t), True{}) == (C.BT(len, t), D.list_eq(UPL(_), UPL(SLN(len, t, j, 0n)))) : D.Bytes & Bool}
      %Equal.sym(L32(), List.take(&2, U32, List.drop(&2, U32, X(len, t), n(j)), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, X(len, t), n(j)))) :
        {(C.BT(len, t), True{}) == (C.BT(len, t), D.list_eq(Nil{}, UPL(_))) : D.Bytes & Bool}
      {==}
    case False{}:
      +hne = Equal.trans(Bool, Nat.is_eq(n(left), 0n), U32.is_zero(left), False{}, Equal.sym(Bool, U32.is_zero(left), Nat.is_eq(n(left), 0n), U.is_zero_to_nat(left)), hz)
      +h1 = N.le_ne(0n, n(left), N.le_zero_l(n(left)), Equal.trans(Bool, Nat.is_eq(0n, n(left)), Nat.is_eq(n(left), 0n), False{}, N.eq_comm(0n, n(left)), hne))
      +k = Nat.sub(n(left), 1n)
      +hk = U.to_nat_sub_le(left, 1, Equal.trans(Bool, U32.is_le(1, left), Nat.is_le(n(1), n(left)), True{}, U.is_le_to_nat(1, left), h1))
      +el = {Equal.sym(Nat, Nat.add(1n, k), n(left), N.le_sub_add(1n, n(left), h1)) : {n(left) == 1n+k : Nat}}
      +hi2 = {%el : {Nat.is_le(Nat.add(n(i), _), n(len)) == True{} : Bool}; hi : {Nat.is_le(Nat.add(n(i), 1n+k), n(len)) == True{} : Bool}}
      +hj2 = {%el : {Nat.is_le(Nat.add(n(j), _), n(len)) == True{} : Bool}; hj : {Nat.is_le(Nat.add(n(j), 1n+k), n(len)) == True{} : Bool}}
      +up_c = U32.is_eq(NS.up(C.AT(len, t, i)), NS.up(C.AT(len, t, j)))
      %Equal.sym(D.Bytes & (U32 & U32), BY.at2(C.BT(len, t), i, j), (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))), S.at2_eq(len, t, i, j)) :
        SCR(len, t, i, j, n(left), NS.same_ci.fin(NS.same_ci.loop(q, NS.same_ci.next(_, i, j, left))))
      %Equal.sym(Nat, n(left), 1n+k, el) : SCR(len, t, i, j, _, NS.same_ci.fin(NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), up_c})))
      %Equal.sym(L32(), SLN(len, t, i, 1n+k), C.AT(len, t, i) <> SLN(len, t, (i + 1 : U32), k), scons(len, t, d, i, k, h, hi2)) :
        {NS.same_ci.fin(NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), up_c})) ==
          (C.BT(len, t), D.list_eq(UPL(_), UPL(SLN(len, t, j, 1n+k)))) : D.Bytes & Bool}
      %Equal.sym(L32(), SLN(len, t, j, 1n+k), C.AT(len, t, j) <> SLN(len, t, (j + 1 : U32), k), scons(len, t, d, j, k, h, hj2)) :
        {NS.same_ci.fin(NS.same_ci.loop(q, NS.Sc{C.BT(len, t), (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), up_c})) ==
          (C.BT(len, t), D.list_eq(UPL(C.AT(len, t, i) <> SLN(len, t, (i + 1 : U32), k)), UPL(_))) : D.Bytes & Bool}
      +ha = {%Equal.sym(Nat, Nat.add(n((i + 1 : U32)), n((left - 1 : U32))), Nat.add(Nat.add(n(i), 1n), k), ij1(len, t, d, i, left, k, h, hi2, hk)) : {Nat.is_le(_, n(len)) == True{} : Bool}; le_add1(n(i), k, n(len), hi2) : {Nat.is_le(Nat.add(n((i + 1 : U32)), n((left - 1 : U32))), n(len)) == True{} : Bool}}
      +hb = {%Equal.sym(Nat, Nat.add(n((j + 1 : U32)), n((left - 1 : U32))), Nat.add(Nat.add(n(j), 1n), k), ij1(len, t, d, j, left, k, h, hj2, hk)) : {Nat.is_le(_, n(len)) == True{} : Bool}; le_add1(n(j), k, n(len), hj2) : {Nat.is_le(Nat.add(n((j + 1 : U32)), n((left - 1 : U32))), n(len)) == True{} : Bool}}
      +hc = {%Equal.sym(Nat, n((left - 1 : U32)), k, hk) : {Nat.is_lt(_, q) == True{} : Bool}; {%el : {Nat.is_lt(_, 1n+q) == True{} : Bool}; hm : {Nat.is_lt(1n+k, 1n+q) == True{} : Bool}} : {Nat.is_lt(n((left - 1 : U32)), q) == True{} : Bool}}
      sc.c(up_c, q, len, t, d, i, j, left, k, hk, {==}, ih(ha, hb, hc))

law sc_go:
  for +m: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +i: U32
  for +j: U32
  for +left: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hi: {Nat.is_le(Nat.add(n(i), n(left)), n(len)) == True{} : Bool}
  for +hj: {Nat.is_le(Nat.add(n(j), n(left)), n(len)) == True{} : Bool}
  for +hm: {Nat.is_lt(n(left), m) == True{} : Bool}
  SCR(len, t, i, j, n(left), NS.same_ci.fin(NS.same_ci.loop(m, NS.Sc{C.BT(len, t), i, j, left, True{}})))

def sc_go(m, len, t, d, i, j, left, h, hi, hj, hm):
  match m:
    case 0n:
      Empty.absurd(SCR(len, t, i, j, n(left), NS.same_ci.fin(NS.same_ci.loop(0n, NS.Sc{C.BT(len, t), i, j, left, True{}}))),
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(n(left), 0n), True{}, Equal.sym(Bool, Nat.is_lt(n(left), 0n), False{}, N.lt_zero(n(left))), hm)))
    case 1n+(+q):
      sc.z(U32.is_zero(left), q, len, t, d, i, j, left, h, hi, hj, hm, {==},
        ha => hb => hc => sc_go(q, len, t, d, (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), h, ha, hb, hc))

def SLX(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg) -> L32():
  match x:
    case NS.Rg{+a, +z}:
      W.SL(len, t, a, z)

# The texts of two ranges, upper-cased, compared.
def CI(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg, +y: NS.Rg) -> Bool:
  String.eq(String.to_upper(WT.TX(len, t, x)), String.to_upper(WT.TX(len, t, y)))

def ci_list(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg, +y: NS.Rg) -> {CI(len, t, x, y) == D.list_eq(UPL(SLX(len, t, x)), UPL(SLX(len, t, y))) : Bool}:
  match x y:
    case NS.Rg{+a, +z} NS.Rg{+c, +e}:
      %Equal.sym(String, String.to_upper(NR.chars(W.SL(len, t, a, z))), NR.chars(UPL(W.SL(len, t, a, z))), upper_chars(W.SL(len, t, a, z))) :
        {String.eq(_, String.to_upper(NR.chars(W.SL(len, t, c, e)))) == D.list_eq(UPL(W.SL(len, t, a, z)), UPL(W.SL(len, t, c, e))) : Bool}
      %Equal.sym(String, String.to_upper(NR.chars(W.SL(len, t, c, e))), NR.chars(UPL(W.SL(len, t, c, e))), upper_chars(W.SL(len, t, c, e))) :
        {String.eq(NR.chars(UPL(W.SL(len, t, a, z))), _) == D.list_eq(UPL(W.SL(len, t, a, z)), UPL(W.SL(len, t, c, e))) : Bool}
      RD.seq(UPL(W.SL(len, t, a, z)), UPL(W.SL(len, t, c, e)))

def sl_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  {List.length(&2, U32, UPL(W.SL(len, t, a, z))) == n((z - a : U32)) : Nat}:
  %Equal.sym(Nat, List.length(&2, U32, UPL(W.SL(len, t, a, z))), List.length(&2, U32, W.SL(len, t, a, z)), upl_len(W.SL(len, t, a, z))) : {_ == n((z - a : U32)) : Nat}
  AL.slice_len(X(len, t), n(a), n((z - a : U32)), %AL.len_x(len, t, d, h) : {Nat.is_le(Nat.add(n(a), n((z - a : U32))), _) == True{} : Bool}; W.pv_put(len, a, z, hp))

def sci.q(+q0: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32, +e: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +hpy: {W.PV(len, NS.Rg{c, e}) == True{} : Bool},
  +hq: {U32.is_eq((z - a : U32), (e - c : U32)) == q0 : Bool}) ->
  {NS.same_ci.fin(NS.same_ci.loop(1n+n((z - a : U32)), NS.Sc{C.BT(len, t), a, c, (z - a : U32), q0})) == (C.BT(len, t), CI(len, t, NS.Rg{a, z}, NS.Rg{c, e})) : D.Bytes & Bool}:
  match q0:
    case True{}:
      +eq = U.is_eq_true((z - a : U32), (e - c : U32), hq)
      +hj = {%Equal.sym(U32, (z - a : U32), (e - c : U32), eq) : {Nat.is_le(Nat.add(n(c), n(_)), n(len)) == True{} : Bool}; W.pv_put(len, c, e, hpy) : {Nat.is_le(Nat.add(n(c), n((z - a : U32))), n(len)) == True{} : Bool}}
      %Equal.sym(Bool, CI(len, t, NS.Rg{a, z}, NS.Rg{c, e}), D.list_eq(UPL(W.SL(len, t, a, z)), UPL(W.SL(len, t, c, e))), ci_list(len, t, NS.Rg{a, z}, NS.Rg{c, e})) :
        {NS.same_ci.fin(NS.same_ci.loop(1n+n((z - a : U32)), NS.Sc{C.BT(len, t), a, c, (z - a : U32), True{}})) == (C.BT(len, t), _) : D.Bytes & Bool}
      %eq :
        {NS.same_ci.fin(NS.same_ci.loop(1n+n((z - a : U32)), NS.Sc{C.BT(len, t), a, c, (z - a : U32), True{}})) == (C.BT(len, t), D.list_eq(UPL(W.SL(len, t, a, z)), UPL(D.slice(X(len, t), n(c), n(_))))) : D.Bytes & Bool}
      sc_go(1n+n((z - a : U32)), len, t, d, a, c, (z - a : U32), h, W.pv_put(len, a, z, hpx), hj, {%N.le_succ_lt(n((z - a : U32)), 1n+n((z - a : U32))) : {_ == True{} : Bool}; N.le_refl(n((z - a : U32))) : {Nat.is_lt(n((z - a : U32)), 1n+n((z - a : U32))) == True{} : Bool}})
    case False{}:
      +hne = {%U.is_eq_to_nat((z - a : U32), (e - c : U32)) : {_ == False{} : Bool}; hq : {Nat.is_eq(n((z - a : U32)), n((e - c : U32))) == False{} : Bool}}
      +hl = {%Equal.sym(Nat, List.length(&2, U32, UPL(W.SL(len, t, a, z))), n((z - a : U32)), sl_len(len, t, d, a, z, h, hpx)) : {Nat.is_eq(_, List.length(&2, U32, UPL(W.SL(len, t, c, e)))) == False{} : Bool};
        %Equal.sym(Nat, List.length(&2, U32, UPL(W.SL(len, t, c, e))), n((e - c : U32)), sl_len(len, t, d, c, e, h, hpy)) : {Nat.is_eq(n((z - a : U32)), _) == False{} : Bool};
        hne : {Nat.is_eq(List.length(&2, U32, UPL(W.SL(len, t, a, z))), List.length(&2, U32, UPL(W.SL(len, t, c, e)))) == False{} : Bool}}
      %Equal.sym(NS.Sc, NS.same_ci.loop(1n+n((z - a : U32)), NS.Sc{C.BT(len, t), a, c, (z - a : U32), False{}}), NS.Sc{C.BT(len, t), a, c, (z - a : U32), False{}}, sc_false(1n+n((z - a : U32)), len, t, a, c, (z - a : U32))) :
        {NS.same_ci.fin(_) == (C.BT(len, t), CI(len, t, NS.Rg{a, z}, NS.Rg{c, e})) : D.Bytes & Bool}
      %Equal.sym(Bool, CI(len, t, NS.Rg{a, z}, NS.Rg{c, e}), D.list_eq(UPL(W.SL(len, t, a, z)), UPL(W.SL(len, t, c, e))), ci_list(len, t, NS.Rg{a, z}, NS.Rg{c, e})) : {(C.BT(len, t), False{}) == (C.BT(len, t), _) : D.Bytes & Bool}
      %Equal.sym(Bool, D.list_eq(UPL(W.SL(len, t, a, z)), UPL(W.SL(len, t, c, e))), False{}, AL.list_eq_len(UPL(W.SL(len, t, a, z)), UPL(W.SL(len, t, c, e)), hl)) : {(C.BT(len, t), False{}) == (C.BT(len, t), _) : D.Bytes & Bool}
      {==}

# same_ci compares the two ranges' texts up to case.
def same_ci_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: NS.Rg, +y: NS.Rg,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hpx: {W.PV(len, x) == True{} : Bool}, +hpy: {W.PV(len, y) == True{} : Bool}) ->
  {NS.same_ci(C.BT(len, t), x, y) == (C.BT(len, t), CI(len, t, x, y)) : D.Bytes & Bool}:
  match x y:
    case NS.Rg{+a, +z} NS.Rg{+c, +e}:
      sci.q(U32.is_eq((z - a : U32), (e - c : U32)), len, t, d, a, z, c, e, h, hpx, hpy, {==})

# ---------------------------------------------------------------------------
# member_ci, distinct
# ---------------------------------------------------------------------------

def Rgs() -> Data:
  List<&2, NS.Rg>

def MEM(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg, ys: Rgs()) -> Bool:
  B.Alts.member(String.to_upper(WT.TX(len, t, x)), K.TXS(len, t, ys))

law or_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}

def or_assoc(a, b, c):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mci.k(+hit: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +x: NS.Rg, +y: NS.Rg,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hpx: {W.PV(len, x) == True{} : Bool}, +hpy: {W.PV(len, y) == True{} : Bool}) ->
  {NS.member_ci.step((C.BT(len, t), hit), x, y) == (C.BT(len, t), Bool.or(hit, CI(len, t, x, y))) : D.Bytes & Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      same_ci_t(len, t, d, x, y, h, hpx, hpy)

law member_t:
  for +ys: Rgs()
  for +hit: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +x: NS.Rg
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hpx: {W.PV(len, x) == True{} : Bool}
  for +hps: {K.ALLPV(len, ys) == True{} : Bool}
  {NS.member_ci(ys, (C.BT(len, t), hit), x) == (C.BT(len, t), Bool.or(hit, MEM(len, t, x, ys))) : D.Bytes & Bool}

def member_t(ys, hit, len, t, d, x, h, hpx, hps):
  match ys:
    case Nil{}:
      %Equal.sym(Bool, Bool.or(hit, False{}), hit, N.or_false_r(hit)) : {(C.BT(len, t), hit) == (C.BT(len, t), _) : D.Bytes & Bool}
      {==}
    case Con{+y, +r}:
      +hpy = N.and_true_l(W.PV(len, y), K.ALLPV(len, r), hps)
      +hpr = N.and_true_r(W.PV(len, y), K.ALLPV(len, r), hps)
      +ci = CI(len, t, x, y)
      %Equal.sym(D.Bytes & Bool, NS.member_ci.step((C.BT(len, t), hit), x, y), (C.BT(len, t), Bool.or(hit, ci)), mci.k(hit, len, t, d, x, y, h, hpx, hpy)) :
        {NS.member_ci(r, _, x) == (C.BT(len, t), Bool.or(hit, MEM(len, t, x, Con{y, r}))) : D.Bytes & Bool}
      %Equal.sym(D.Bytes & Bool, NS.member_ci(r, (C.BT(len, t), Bool.or(hit, ci)), x), (C.BT(len, t), Bool.or(Bool.or(hit, ci), MEM(len, t, x, r))), member_t(r, Bool.or(hit, ci), len, t, d, x, h, hpx, hpr)) :
        {_ == (C.BT(len, t), Bool.or(hit, MEM(len, t, x, Con{y, r}))) : D.Bytes & Bool}
      %Equal.sym(Bool, Bool.or(Bool.or(hit, ci), MEM(len, t, x, r)), Bool.or(hit, Bool.or(ci, MEM(len, t, x, r))), or_assoc(hit, ci, MEM(len, t, x, r))) : {(C.BT(len, t), _) == (C.BT(len, t), Bool.or(hit, MEM(len, t, x, Con{y, r}))) : D.Bytes & Bool}
      {==}

law distinct_t:
  for +xs: Rgs()
  for +ok: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hps: {K.ALLPV(len, xs) == True{} : Bool}
  {NS.distinct(xs, (C.BT(len, t), ok)) == (C.BT(len, t), Bool.and(ok, B.Alts.distinct(K.TXS(len, t, xs)))) : D.Bytes & Bool}

def distinct_t(xs, ok, len, t, d, h, hps):
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(ok, True{}), ok, N.and_true_r_id(ok)) : {(C.BT(len, t), ok) == (C.BT(len, t), _) : D.Bytes & Bool}
      {==}
    case Con{+x, +r}:
      +hpx = N.and_true_l(W.PV(len, x), K.ALLPV(len, r), hps)
      +hpr = N.and_true_r(W.PV(len, x), K.ALLPV(len, r), hps)
      +M = MEM(len, t, x, r)
      +Dr = B.Alts.distinct(K.TXS(len, t, r))
      -RHS = {(C.BT(len, t), Bool.and(ok, B.Alts.distinct(K.TXS(len, t, Con{x, r})))) : D.Bytes & Bool}
      %Equal.sym(D.Bytes & Bool, NS.member_ci(r, (C.BT(len, t), False{}), x), (C.BT(len, t), Bool.or(False{}, M)), member_t(r, False{}, len, t, d, x, h, hpx, hpr)) :
        {NS.distinct(r, NS.distinct.k(ok, _)) == RHS : D.Bytes & Bool}
      %Equal.sym(D.Bytes & Bool, NS.distinct(r, (C.BT(len, t), Bool.and(ok, Bool.not(M)))), (C.BT(len, t), Bool.and(Bool.and(ok, Bool.not(M)), Dr)), distinct_t(r, Bool.and(ok, Bool.not(M)), len, t, d, h, hpr)) :
        {_ == RHS : D.Bytes & Bool}
      %Equal.sym(Bool, Bool.and(Bool.and(ok, Bool.not(M)), Dr), Bool.and(ok, Bool.and(Bool.not(M), Dr)), LS.and_assoc(ok, Bool.not(M), Dr)) :
        {(C.BT(len, t), _) == RHS : D.Bytes & Bool}
      {==}
