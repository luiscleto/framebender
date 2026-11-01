import Base
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_b_fasteq.bend as FE
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as AL
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_cut.bend as K
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/fast.bend as F
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_find.bend as PF
import lawful-bytes@0.1.1.0/proof_list.bend as BL
import lawful-fields@0.1.1.0/defs.bend as FD
import lawful-fields@0.1.1.0/LAWS.bend as FL
import lawful-fields@0.1.1.0/PROOF.bend as FP
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The byte splitter's scans on a well-formed line: the first c from a (J),
# and what count and nth give, against the split of the range's bytes
# (proof_s_cut.bend's SP). Generalized from proof_b_alleles_loop.bend (which
# has them for commas). Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def LL() -> Data:
  List<&2, List<&2, U32>>

def X(+len: U32, +t: AT.Tree<U32>) -> L32():
  D.view(C.BT(len, t))

# The first c in a .. z-1, or z.
def J(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32) -> U32:
  Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), a, z, c))

def find_step(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32) ->
  {F.find(C.BT(len, t), a, z, c) == (C.BT(len, t), J(len, t, a, z, c)) : D.Bytes & U32}:
  FE.find_pair(C.BT(len, t), a, z, c)

def j_val(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  {n(J(len, t, a, z, c)) == D.first(X(len, t), n(a), n(z), c) : Nat}:
  Equal.trans(Nat, n(J(len, t, a, z, c)), n(Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), a, z, c))), D.first(X(len, t), n(a), n(z), c),
    Equal.cong(D.Bytes & U32, Nat, r => U32.to_nat(Pair.snd(D.Bytes, U32, r)), F.find(C.BT(len, t), a, z, c), BY.find(C.BT(len, t), a, z, c), FE.find_eq(C.BT(len, t), d, a, z, c, h, AL.le_u(a, z, haz), hzl, hc)),
    PF.find_view_t(len, t, d, a, z, c, h, AL.le_u(a, z, haz), hzl, hc))

def j_range(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  {Bool.and(Nat.is_le(n(a), n(J(len, t, a, z, c))), Nat.is_le(n(J(len, t, a, z, c)), n(z))) == True{} : Bool}:
  %Equal.sym(Nat, n(J(len, t, a, z, c)), D.first(X(len, t), n(a), n(z), c), j_val(len, t, d, a, z, c, h, haz, hzl, hc)) :
    {Bool.and(Nat.is_le(n(a), _), Nat.is_le(_, n(z))) == True{} : Bool}
  BL.first_range(X(len, t), n(a), n(z), c, haz, %AL.len_x(len, t, d, h) : {Nat.is_le(n(z), _) == True{} : Bool}; hzl)

def j_lo(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) -> {Nat.is_le(n(a), n(J(len, t, a, z, c))) == True{} : Bool}:
  N.and_true_l(Nat.is_le(n(a), n(J(len, t, a, z, c))), Nat.is_le(n(J(len, t, a, z, c)), n(z)), j_range(len, t, d, a, z, c, h, haz, hzl, hc))

def j_hi(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) -> {Nat.is_le(n(J(len, t, a, z, c)), n(z)) == True{} : Bool}:
  N.and_true_r(Nat.is_le(n(a), n(J(len, t, a, z, c))), Nat.is_le(n(J(len, t, a, z, c)), n(z)), j_range(len, t, d, a, z, c, h, haz, hzl, hc))

def j_hit(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool},
  +hlt: {Nat.is_lt(n(J(len, t, a, z, c)), n(z)) == True{} : Bool}) ->
  {List.get(&2, U32, X(len, t), n(J(len, t, a, z, c))) == Some{c} : Maybe<&2, U32>}:
  +VW = X(len, t)
  +fst = D.first(VW, n(a), n(z), c)
  +ev = j_val(len, t, d, a, z, c, h, haz, hzl, hc)
  %Equal.sym(Nat, n(J(len, t, a, z, c)), fst, ev) : {List.get(&2, U32, VW, _) == Some{c} : Maybe<&2, U32>}
  AL.has_get(VW, fst, c, BL.first_hit(VW, n(a), n(z), c, haz, %AL.len_x(len, t, d, h) : {Nat.is_le(n(z), _) == True{} : Bool}; hzl,
    %ev : {Nat.is_lt(_, n(z)) == True{} : Bool}; hlt))

# The pieces of a .. z-1: the bytes up to the first c, then those after it.
def BS(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> L32():
  D.slice(X(len, t), n(a), Nat.sub(n(z), n(a)))

def TS(+len: U32, +t: AT.Tree<U32>, +j: U32, +z: U32, +c: U32) -> LL():
  LS.tsplit(BS(len, t, j, z), c)

def sp_first(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  {K.SP(len, t, a, z, c) == Con{BS(len, t, a, J(len, t, a, z, c)), TS(len, t, J(len, t, a, z, c), z, c)} : LL()}:
  +VW = X(len, t)
  +na = n(a)
  +nz = n(z)
  +ev = j_val(len, t, d, a, z, c, h, haz, hzl, hc)
  %Equal.sym(Nat, n(J(len, t, a, z, c)), D.first(VW, na, nz, c), ev) :
    {K.SP(len, t, a, z, c) == Con{D.slice(VW, na, Nat.sub(_, na)), LS.tsplit(D.slice(VW, _, Nat.sub(nz, _)), c)} : LL()}
  LS.spl(VW, na, nz, c)

# The pieces after a c at j < z.
def ts_next(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(z)) == True{} : Bool},
  +hg: {List.get(&2, U32, X(len, t), n(j)) == Some{c} : Maybe<&2, U32>}) ->
  {TS(len, t, j, z, c) == K.SP(len, t, (j + 1 : U32), z, c) : LL()}:
  +VW = X(len, t)
  +nj = n(j)
  +nz = n(z)
  %Equal.sym(Nat, n((j + 1 : U32)), Nat.add(nj, 1n), AL.inc_len(len, t, d, j, h, N.lt_le_trans(nj, nz, n(len), hlt, hzl))) :
    {TS(len, t, j, z, c) == FD.split(D.slice(VW, _, Nat.sub(nz, _)), c) : LL()}
  LS.ts_lt(VW, nj, nz, c, hlt, hg)

def ts_last(+len: U32, +t: AT.Tree<U32>, +j: U32, +z: U32, +c: U32, +hjz: {n(j) == n(z) : Nat}) ->
  {TS(len, t, j, z, c) == Nil{} : LL()}:
  %Equal.sym(Nat, n(j), n(z), hjz) : {LS.tsplit(D.slice(X(len, t), _, Nat.sub(n(z), _)), c) == Nil{} : LL()}
  LS.ts_eq(X(len, t), n(z), c)

# ---------------------------------------------------------------------------
# Fuel
# ---------------------------------------------------------------------------

def u_ne(+x: U32, +y: U32, +h: {U32.is_eq(x, y) == False{} : Bool}) -> {Nat.is_eq(n(x), n(y)) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(n(x), n(y)), U32.is_eq(x, y), False{}, Equal.sym(Bool, U32.is_eq(x, y), Nat.is_eq(n(x), n(y)), U.is_eq_to_nat(x, y)), h)

def u_eq(+x: U32, +y: U32, +h: {U32.is_eq(x, y) == True{} : Bool}) -> {n(x) == n(y) : Nat}:
  Equal.cong(U32, Nat, w => U32.to_nat(w), x, y, U.is_eq_true(x, y, h))

# j <= z and j != z: j < z.
def lt_of(+j: U32, +z: U32, +hle: {Nat.is_le(n(j), n(z)) == True{} : Bool}, +hne: {U32.is_eq(j, z) == False{} : Bool}) ->
  {Nat.is_lt(n(j), n(z)) == True{} : Bool}:
  %N.le_succ_lt(n(j), n(z)) : {_ == True{} : Bool}
  N.le_ne(n(j), n(z), hle, u_ne(j, z, hne))

# No fuel cannot cover a non-empty need.
def no_fuel(-A: Type, +a: Nat, +z: Nat, +haz: {Nat.is_le(a, z) == True{} : Bool}, +hm: {Nat.is_lt(z, Nat.add(a, 0n)) == True{} : Bool}) -> A:
  +h1 = {%N.add_zero(a) : {Nat.is_lt(z, _) == True{} : Bool}; hm : {Nat.is_lt(z, a) == True{} : Bool}}
  Empty.absurd(A, P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(a, a), True{}, Equal.sym(Bool, Nat.is_lt(a, a), False{}, N.lt_irrefl(a)), N.le_lt_trans(a, z, a, haz, h1))))

# The fuel left after a step to j + 1 >= a + 1.
def fuel_step(+a: Nat, +j: Nat, +z: Nat, +q: Nat, +haj: {Nat.is_le(a, j) == True{} : Bool},
  +hm: {Nat.is_lt(z, Nat.add(a, 1n+q)) == True{} : Bool}) -> {Nat.is_lt(z, Nat.add(Nat.add(j, 1n), q)) == True{} : Bool}:
  +h1 = {%N.add_succ(a, q) : {Nat.is_lt(z, _) == True{} : Bool}; hm : {Nat.is_lt(z, 1n+Nat.add(a, q)) == True{} : Bool}}
  +h2 = {%Equal.sym(Bool, Nat.is_le(1n+z, 1n+Nat.add(a, q)), Nat.is_lt(z, 1n+Nat.add(a, q)), N.le_succ_lt(z, 1n+Nat.add(a, q))) : {_ == True{} : Bool}; h1 : {Nat.is_le(z, Nat.add(a, q)) == True{} : Bool}}
  +h3 = N.le_trans(z, Nat.add(a, q), Nat.add(j, q), h2, N.le_add_mono_r(q, a, j, haj))
  %Equal.sym(Nat, Nat.add(Nat.add(j, 1n), q), Nat.add(q, Nat.add(j, 1n)), N.add_comm(Nat.add(j, 1n), q)) : {Nat.is_lt(z, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(j, 1n), 1n+j, N.add_one(j)) : {Nat.is_lt(z, Nat.add(q, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(q, 1n+j), 1n+Nat.add(q, j), N.add_succ(q, j)) : {Nat.is_lt(z, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(q, j), Nat.add(j, q), N.add_comm(q, j)) : {Nat.is_lt(z, 1n+_) == True{} : Bool}
  %N.le_succ_lt(z, 1n+Nat.add(j, q)) : {_ == True{} : Bool}
  h3

# ---------------------------------------------------------------------------
# count: one less than the pieces
# ---------------------------------------------------------------------------

def BT(+len: U32, +t: AT.Tree<U32>) -> D.Bytes:
  C.BT(len, t)

def NP(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32) -> Nat:
  List.length(&2, List<&2, U32>, K.SP(len, t, a, z, c))

def CNT(+len: U32, +t: AT.Tree<U32>, +k: Nat, +a: U32, +z: U32, +c: U32, -r: D.Bytes & Nat) -> Type:
  &k2: Nat -> ({r == (C.BT(len, t), k2) : D.Bytes & Nat} & {Nat.add(k2, 1n) == Nat.add(k, NP(len, t, a, z, c)) : Nat})

def cl_done(+q: Nat, +len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32, +k: Nat) ->
  {NS.count.loop(q, NS.Cn{C.BT(len, t), a, z, c, k, True{}}) == NS.Cn{C.BT(len, t), a, z, c, k, True{}} : NS.Cn}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

# The pieces of a .. z-1 when its first c is z: one.
def np_last(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool},
  +he: {U32.is_eq(J(len, t, a, z, c), z) == True{} : Bool}) -> {NP(len, t, a, z, c) == 1n : Nat}:
  %Equal.sym(LL(), K.SP(len, t, a, z, c), Con{BS(len, t, a, J(len, t, a, z, c)), TS(len, t, J(len, t, a, z, c), z, c)}, sp_first(len, t, d, a, z, c, h, haz, hzl, hc)) : {List.length(&2, List<&2, U32>, _) == 1n : Nat}
  %Equal.sym(LL(), TS(len, t, J(len, t, a, z, c), z, c), Nil{}, ts_last(len, t, J(len, t, a, z, c), z, c, u_eq(J(len, t, a, z, c), z, he))) :
    {List.length(&2, List<&2, U32>, Con{BS(len, t, a, J(len, t, a, z, c)), _}) == 1n : Nat}
  {==}

# ... and when it is below z: one more than those after it.
def np_next(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool},
  +hlt: {Nat.is_lt(n(J(len, t, a, z, c)), n(z)) == True{} : Bool}) ->
  {K.SP(len, t, a, z, c) == Con{BS(len, t, a, J(len, t, a, z, c)), K.SP(len, t, (J(len, t, a, z, c) + 1 : U32), z, c)} : LL()}:
  +j = J(len, t, a, z, c)
  %Equal.sym(LL(), K.SP(len, t, a, z, c), Con{BS(len, t, a, j), TS(len, t, j, z, c)}, sp_first(len, t, d, a, z, c, h, haz, hzl, hc)) :
    {_ == Con{BS(len, t, a, j), K.SP(len, t, (j + 1 : U32), z, c)} : LL()}
  %Equal.sym(LL(), TS(len, t, j, z, c), K.SP(len, t, (j + 1 : U32), z, c), ts_next(len, t, d, j, z, c, h, hzl, hlt, j_hit(len, t, d, a, z, c, h, haz, hzl, hc, hlt))) :
    {Con{BS(len, t, a, j), _} == Con{BS(len, t, a, j), K.SP(len, t, (j + 1 : U32), z, c)} : LL()}
  {==}

def j1_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(z)) == True{} : Bool}) -> {Nat.is_le(n((j + 1 : U32)), n(z)) == True{} : Bool}:
  %Equal.sym(Nat, n((j + 1 : U32)), Nat.add(n(j), 1n), AL.inc_len(len, t, d, j, h, N.lt_le_trans(n(j), n(z), n(len), hlt, hzl))) : {Nat.is_le(_, n(z)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n(j), 1n), 1n+n(j), N.add_one(n(j))) : {Nat.is_le(_, n(z)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(1n+n(j), n(z)), Nat.is_lt(n(j), n(z)), N.le_succ_lt(n(j), n(z))) : {_ == True{} : Bool}
  hlt

def cnt.next(+q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32, +k: Nat,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool},
  +hlt: {Nat.is_lt(n(J(len, t, a, z, c)), n(z)) == True{} : Bool},
  r: CNT(len, t, 1n+k, (J(len, t, a, z, c) + 1 : U32), z, c, NS.count.fin(NS.count.loop(q, NS.Cn{C.BT(len, t), (J(len, t, a, z, c) + 1 : U32), z, c, 1n+k, False{}})))) ->
  CNT(len, t, k, a, z, c, NS.count.fin(NS.count.loop(q, NS.Cn{C.BT(len, t), (J(len, t, a, z, c) + 1 : U32), z, c, 1n+k, False{}}))):
  (+k2, e) = r
  (eq, ek) = e
  +j1 = (J(len, t, a, z, c) + 1 : U32)
  +L = NP(len, t, j1, z, c)
  +ek2 = {%Equal.sym(LL(), K.SP(len, t, a, z, c), Con{BS(len, t, a, J(len, t, a, z, c)), K.SP(len, t, j1, z, c)}, np_next(len, t, d, a, z, c, h, haz, hzl, hc, hlt)) : {Nat.add(k2, 1n) == Nat.add(k, List.length(&2, List<&2, U32>, _)) : Nat};
    %Equal.sym(Nat, Nat.add(k, 1n+L), 1n+Nat.add(k, L), N.add_succ(k, L)) : {Nat.add(k2, 1n) == _ : Nat};
    ek : {Nat.add(k2, 1n) == Nat.add(k, NP(len, t, a, z, c)) : Nat}}
  (k2, (eq, ek2))

def cnt.k(+e: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32, +k: Nat,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool},
  +hm: {Nat.is_lt(n(z), Nat.add(n(a), 1n+q)) == True{} : Bool},
  +he: {U32.is_eq(J(len, t, a, z, c), z) == e : Bool},
  ih: @+a2: U32 -> @+k2: Nat -> {Nat.is_le(n(a2), n(z)) == True{} : Bool} -> {Nat.is_lt(n(z), Nat.add(n(a2), q)) == True{} : Bool} ->
    CNT(len, t, k2, a2, z, c, NS.count.fin(NS.count.loop(q, NS.Cn{C.BT(len, t), a2, z, c, k2, False{}})))) ->
  CNT(len, t, k, a, z, c, NS.count.fin(NS.count.loop(q, NS.count.if(e, C.BT(len, t), J(len, t, a, z, c), z, c, k)))):
  match e:
    case True{}:
      +j = J(len, t, a, z, c)
      %Equal.sym(NS.Cn, NS.count.loop(q, NS.Cn{C.BT(len, t), j, z, c, k, True{}}), NS.Cn{C.BT(len, t), j, z, c, k, True{}}, cl_done(q, len, t, j, z, c, k)) :
        CNT(len, t, k, a, z, c, NS.count.fin(_))
      (k, ({==}, {%Equal.sym(Nat, NP(len, t, a, z, c), 1n, np_last(len, t, d, a, z, c, h, haz, hzl, hc, he)) : {Nat.add(k, 1n) == Nat.add(k, _) : Nat}; {==} : {Nat.add(k, 1n) == Nat.add(k, NP(len, t, a, z, c)) : Nat}}))
    case False{}:
      +j = J(len, t, a, z, c)
      +hlt = lt_of(j, z, j_hi(len, t, d, a, z, c, h, haz, hzl, hc), he)
      +j1 = (j + 1 : U32)
      +ej = AL.inc_len(len, t, d, j, h, N.lt_le_trans(n(j), n(z), n(len), hlt, hzl))
      +hm2 = {%Equal.sym(Nat, n(j1), Nat.add(n(j), 1n), ej) : {Nat.is_lt(n(z), Nat.add(_, q)) == True{} : Bool}; fuel_step(n(a), n(j), n(z), q, j_lo(len, t, d, a, z, c, h, haz, hzl, hc), hm) : {Nat.is_lt(n(z), Nat.add(n(j1), q)) == True{} : Bool}}
      cnt.next(q, len, t, d, a, z, c, k, h, haz, hzl, hc, hlt, ih(j1, 1n+k, j1_le(len, t, d, j, z, h, hzl, hlt), hm2))

law cnt_go:
  for +m: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +a: U32
  for +z: U32
  for +c: U32
  for +k: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}
  for +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +hm: {Nat.is_lt(n(z), Nat.add(n(a), m)) == True{} : Bool}
  CNT(len, t, k, a, z, c, NS.count.fin(NS.count.loop(m, NS.Cn{C.BT(len, t), a, z, c, k, False{}})))

def cnt_go(m, len, t, d, a, z, c, k, h, haz, hzl, hc, hm):
  match m:
    case 0n:
      no_fuel(CNT(len, t, k, a, z, c, NS.count.fin(NS.count.loop(0n, NS.Cn{C.BT(len, t), a, z, c, k, False{}}))), n(a), n(z), haz, hm)
    case 1n+(+q):
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, z, c), (C.BT(len, t), J(len, t, a, z, c)), find_step(len, t, a, z, c)) :
        CNT(len, t, k, a, z, c, NS.count.fin(NS.count.loop(q, NS.count.next(_, z, c, k))))
      cnt.k(U32.is_eq(J(len, t, a, z, c), z), q, len, t, d, a, z, c, k, h, haz, hzl, hc, hm, {==},
        +a2 => +k2 => h1 => h2 => cnt_go(q, len, t, d, a2, z, c, k2, h, h1, hzl, hc, h2))

# The fuel the scans start with covers the range.
def fuel0(+a: U32, +z: U32, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}) -> {Nat.is_lt(n(z), Nat.add(n(a), 1n+n((z - a : U32)))) == True{} : Bool}:
  %Equal.sym(Nat, n((z - a : U32)), Nat.sub(n(z), n(a)), W.nsub(a, z, haz)) : {Nat.is_lt(n(z), Nat.add(n(a), 1n+_)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n(a), 1n+Nat.sub(n(z), n(a))), 1n+Nat.add(n(a), Nat.sub(n(z), n(a))), N.add_succ(n(a), Nat.sub(n(z), n(a)))) : {Nat.is_lt(n(z), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n(a), Nat.sub(n(z), n(a))), n(z), N.le_sub_add(n(a), n(z), haz)) : {Nat.is_lt(n(z), 1n+_) == True{} : Bool}
  %N.le_succ_lt(n(z), 1n+n(z)) : {_ == True{} : Bool}
  N.le_refl(n(z))

# count gives the number of c in the range.
def count_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  CNT(len, t, 0n, a, z, c, NS.count(C.BT(len, t), NS.Rg{a, z}, c)):
  cnt_go(1n+n((z - a : U32)), len, t, d, a, z, c, 0n, h, haz, hzl, hc, fuel0(a, z, haz))

# The number counted is FD.count of the range's bytes.
def cnt_val(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32, +k2: Nat,
  +ek: {Nat.add(k2, 1n) == Nat.add(0n, NP(len, t, a, z, c)) : Nat}) -> {k2 == FD.count(BS(len, t, a, z), c) : Nat}:
  N.add_cancel_r(1n, k2, FD.count(BS(len, t, a, z), c),
    Equal.trans(Nat, Nat.add(k2, 1n), NP(len, t, a, z, c), Nat.add(FD.count(BS(len, t, a, z), c), 1n), ek, FL.split_length(BS(len, t, a, z), c)))

# ---------------------------------------------------------------------------
# nth: the range of value j (pieces at ',')
# ---------------------------------------------------------------------------

def SLR(+len: U32, +t: AT.Tree<U32>, +r: NS.Rg) -> L32():
  match r:
    case NS.Rg{+a, +z}:
      W.SL(len, t, a, z)

def Ps() -> Data:
  List<&2, List<&2, U32>>

def NTR(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +j: Nat, -r: D.Bytes & NS.Rg) -> Type:
  &R: NS.Rg -> ({r == (C.BT(len, t), R) : D.Bytes & NS.Rg} &
    ({List.get(&2, List<&2, U32>, K.SP(len, t, a, z, 44), j) == Some{SLR(len, t, R)} : Maybe<&2, List<&2, U32>>} & {W.PV(len, R) == True{} : Bool}))

def nl_done(+q: Nat, +len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +j: Nat, +r: NS.Rg) ->
  {NS.nth.loop(q, NS.Nt{C.BT(len, t), a, z, j, r, True{}}) == NS.Nt{C.BT(len, t), a, z, j, r, True{}} : NS.Nt}:
  match q:
    case 0n:
      {==}
    case 1n+s:
      {==}

# Piece 0: up to the first comma.
def nth0(+q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  NTR(len, t, a, z, 0n, NS.nth.fin(NS.nth.loop(q, NS.Nt{C.BT(len, t), a, z, 0n, NS.Rg{a, J(len, t, a, z, 44)}, True{}}))):
  +e = J(len, t, a, z, 44)
  +hae = j_lo(len, t, d, a, z, 44, h, haz, hzl, {==})
  %Equal.sym(NS.Nt, NS.nth.loop(q, NS.Nt{C.BT(len, t), a, z, 0n, NS.Rg{a, e}, True{}}), NS.Nt{C.BT(len, t), a, z, 0n, NS.Rg{a, e}, True{}}, nl_done(q, len, t, a, z, 0n, NS.Rg{a, e})) :
    NTR(len, t, a, z, 0n, NS.nth.fin(_))
  +hg = {%Equal.sym(Ps(), K.SP(len, t, a, z, 44), Con{BS(len, t, a, e), TS(len, t, e, z, 44)}, sp_first(len, t, d, a, z, 44, h, haz, hzl, {==})) :
      {List.get(&2, List<&2, U32>, _, 0n) == Some{W.SL(len, t, a, e)} : Maybe<&2, List<&2, U32>>};
    %Equal.sym(Nat, n((e - a : U32)), Nat.sub(n(e), n(a)), W.nsub(a, e, hae)) : {Some{BS(len, t, a, e)} == Some{D.slice(X(len, t), n(a), _)} : Maybe<&2, List<&2, U32>>};
    {==} : {List.get(&2, List<&2, U32>, K.SP(len, t, a, z, 44), 0n) == Some{W.SL(len, t, a, e)} : Maybe<&2, List<&2, U32>>}}
  (NS.Rg{a, e}, ({==}, (hg, W.pv_mk(len, a, e, hae, N.le_trans(n(e), n(z), n(len), j_hi(len, t, d, a, z, 44, h, haz, hzl, {==}), hzl)))))

def nth.next_t(+q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +k: Nat,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(J(len, t, a, z, 44)), n(z)) == True{} : Bool},
  r: NTR(len, t, (J(len, t, a, z, 44) + 1 : U32), z, k, NS.nth.fin(NS.nth.loop(q, NS.Nt{C.BT(len, t), (J(len, t, a, z, 44) + 1 : U32), z, k, NS.Rg{a, J(len, t, a, z, 44)}, False{}})))) ->
  NTR(len, t, a, z, 1n+k, NS.nth.fin(NS.nth.loop(q, NS.Nt{C.BT(len, t), (J(len, t, a, z, 44) + 1 : U32), z, k, NS.Rg{a, J(len, t, a, z, 44)}, False{}}))):
  (+R, e) = r
  (eq, e2) = e
  (hg, hp) = e2
  +j1 = (J(len, t, a, z, 44) + 1 : U32)
  +hg2 = {%Equal.sym(Ps(), K.SP(len, t, a, z, 44), Con{BS(len, t, a, J(len, t, a, z, 44)), K.SP(len, t, j1, z, 44)}, np_next(len, t, d, a, z, 44, h, haz, hzl, {==}, hlt)) :
      {List.get(&2, List<&2, U32>, _, 1n+k) == Some{SLR(len, t, R)} : Maybe<&2, List<&2, U32>>};
    hg : {List.get(&2, List<&2, U32>, K.SP(len, t, a, z, 44), 1n+k) == Some{SLR(len, t, R)} : Maybe<&2, List<&2, U32>>}}
  (R, (eq, (hg2, hp)))

def nth.k(+e: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +k: Nat,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hm: {Nat.is_lt(n(z), Nat.add(n(a), 1n+q)) == True{} : Bool},
  +hj: {Nat.is_lt(1n+k, NP(len, t, a, z, 44)) == True{} : Bool},
  +he: {U32.is_eq(J(len, t, a, z, 44), z) == e : Bool},
  ih: @+a2: U32 -> @+k2: Nat -> @+r2: NS.Rg -> {Nat.is_le(n(a2), n(z)) == True{} : Bool} -> {Nat.is_lt(n(z), Nat.add(n(a2), q)) == True{} : Bool} ->
    {Nat.is_lt(k2, NP(len, t, a2, z, 44)) == True{} : Bool} ->
    NTR(len, t, a2, z, k2, NS.nth.fin(NS.nth.loop(q, NS.Nt{C.BT(len, t), a2, z, k2, r2, False{}})))) ->
  NTR(len, t, a, z, 1n+k, NS.nth.fin(NS.nth.loop(q, NS.Nt{C.BT(len, t), (J(len, t, a, z, 44) + 1 : U32), z, k, NS.Rg{a, J(len, t, a, z, 44)}, e}))):
  match e:
    case True{}:
      +h1 = {%np_last(len, t, d, a, z, 44, h, haz, hzl, {==}, he) : {Nat.is_lt(1n+k, _) == True{} : Bool}; hj : {Nat.is_lt(k, 0n) == True{} : Bool}}
      Empty.absurd(NTR(len, t, a, z, 1n+k, NS.nth.fin(NS.nth.loop(q, NS.Nt{C.BT(len, t), (J(len, t, a, z, 44) + 1 : U32), z, k, NS.Rg{a, J(len, t, a, z, 44)}, True{}}))),
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, N.lt_zero(k)), h1)))
    case False{}:
      +j = J(len, t, a, z, 44)
      +hlt = lt_of(j, z, j_hi(len, t, d, a, z, 44, h, haz, hzl, {==}), he)
      +j1 = (j + 1 : U32)
      +ej = AL.inc_len(len, t, d, j, h, N.lt_le_trans(n(j), n(z), n(len), hlt, hzl))
      +hm2 = {%Equal.sym(Nat, n(j1), Nat.add(n(j), 1n), ej) : {Nat.is_lt(n(z), Nat.add(_, q)) == True{} : Bool}; fuel_step(n(a), n(j), n(z), q, j_lo(len, t, d, a, z, 44, h, haz, hzl, {==}), hm) : {Nat.is_lt(n(z), Nat.add(n(j1), q)) == True{} : Bool}}
      +hk = {%np_next(len, t, d, a, z, 44, h, haz, hzl, {==}, hlt) :
          {Nat.is_lt(1n+k, List.length(&2, List<&2, U32>, _)) == True{} : Bool}; hj : {Nat.is_lt(k, NP(len, t, j1, z, 44)) == True{} : Bool}}
      nth.next_t(q, len, t, d, a, z, k, h, haz, hzl, hlt, ih(j1, k, NS.Rg{a, j}, j1_le(len, t, d, j, z, h, hzl, hlt), hm2, hk))

law nth_go:
  for +m: Nat
  for +j: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +a: U32
  for +z: U32
  for +r: NS.Rg
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}
  for +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}
  for +hm: {Nat.is_lt(n(z), Nat.add(n(a), m)) == True{} : Bool}
  for +hj: {Nat.is_lt(j, NP(len, t, a, z, 44)) == True{} : Bool}
  NTR(len, t, a, z, j, NS.nth.fin(NS.nth.loop(m, NS.Nt{C.BT(len, t), a, z, j, r, False{}})))

def nth_go(m, j, len, t, d, a, z, r, h, haz, hzl, hm, hj):
  match m j:
    case 0n _:
      no_fuel(NTR(len, t, a, z, j, NS.nth.fin(NS.nth.loop(0n, NS.Nt{C.BT(len, t), a, z, j, r, False{}}))), n(a), n(z), haz, hm)
    case 1n+(+q) 0n:
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, z, 44), (C.BT(len, t), J(len, t, a, z, 44)), find_step(len, t, a, z, 44)) :
        NTR(len, t, a, z, 0n, NS.nth.fin(NS.nth.loop(q, NS.nth.next(_, a, z, 0n))))
      nth0(q, len, t, d, a, z, h, haz, hzl)
    case 1n+(+q) 1n+(+k):
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, z, 44), (C.BT(len, t), J(len, t, a, z, 44)), find_step(len, t, a, z, 44)) :
        NTR(len, t, a, z, 1n+k, NS.nth.fin(NS.nth.loop(q, NS.nth.next(_, a, z, 1n+k))))
      nth.k(U32.is_eq(J(len, t, a, z, 44), z), q, len, t, d, a, z, k, h, haz, hzl, hm, hj, {==},
        +a2 => +k2 => +r2 => h1 => h2 => h3 => nth_go(q, k2, len, t, d, a2, z, r2, h, h1, hzl, h2, h3))

# nth gives the range of value j when there is one.
def nth_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +j: Nat,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hj: {Nat.is_lt(j, NP(len, t, a, z, 44)) == True{} : Bool}) ->
  NTR(len, t, a, z, j, NS.nth(C.BT(len, t), NS.Rg{a, z}, j)):
  nth_go(1n+n((z - a : U32)), j, len, t, d, a, z, NS.Rg{a, a}, h, haz, hzl, fuel0(a, z, haz), hj)
