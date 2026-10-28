import Base
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_run_lem.bend as LM
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_num.bend as NM
import ./proof_b_enc_lem.bend as X
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-bytes/proof_grow.bend as G
import ../lawful-bytes/proof_append.bend as PA
import ../lawful-bytes/proof_seq.bend as Q
import ../lawful-bytes/fast.bend as F
import ./proof_b_fasteq.bend as FE
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_index.bend as I
import ../lawful-arrays/defs.bend as A
import ../lawful-words/defs.bend as W
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# The run's buffer operations on mirrors (C.BT(len, t)): room, put_str.
# Each is named by a Data function of the mirror (the tree it leaves), so the
# run's proofs never carry a Bytes.

# room
# ====

def CAPV(+l: U32, +t: AT.Tree<U32>) -> U32:
  Pair.snd(D.Bytes, U32, BY.capacity(C.BT(l, t)))

def rt.if(c: Bool, +t: AT.Tree<U32>, +e: Nat) -> AT.Tree<U32>:
  match c:
    case True{}:
      t
    case False{}:
      G.gtree(U32.to_nat(U32.shln(1, RD.tdepth(t))), t, G.tnew(e, 0), 0)

# The tree room leaves.
def RT(+l: U32, +t: AT.Tree<U32>, +k: U32) -> AT.Tree<U32>:
  rt.if(U32.is_le((l + k + 8 : U32), CAPV(l, t)), t, NR.depth(((l + k + 8 : U32) * 2 : U32)))

law room_if:
  for +c: Bool
  for +l: U32
  for +t: AT.Tree<U32>
  for +n: U32
  for +hf: {A.full(U32, AT.fromT(U32, t), RD.tdepth(t)) == True{} : Bool}
  {NR.room.if(c, n, C.BT(l, t)) == C.BT(l, rt.if(c, t, NR.depth((n * 2 : U32)))) : D.Bytes}

def room_if(c, l, t, n, hf):
  match c:
    case True{}:
      {==}
    case False{}:
      G.grow_eq(l, t, RD.tdepth(t), NR.depth((n * 2 : U32)), hf)

law room_eq:
  for +l: U32
  for +t: AT.Tree<U32>
  for +k: U32
  for +hf: {A.full(U32, AT.fromT(U32, t), RD.tdepth(t)) == True{} : Bool}
  {NR.room(C.BT(l, t), k) == C.BT(l, RT(l, t, k)) : D.Bytes}

def room_eq(l, t, k, hf):
  +n = (l + k + 8 : U32)
  %Equal.sym(D.Bytes & U32, BY.capacity(C.BT(l, t)), (C.BT(l, t), CAPV(l, t)), O.capacity_pair_t(l, t)) :
    {NR.room.k(n, _) == C.BT(l, RT(l, t, k)) : D.Bytes}
  room_if(U32.is_le(n, CAPV(l, t)), l, t, n, hf)

# room's sizes: (l + k + 8) as a number.
law room_n:
  for +l: U32
  for +k: U32
  for +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(k)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {U32.to_nat((l + k + 8 : U32)) == Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(k)), 8n) : Nat}

def room_n(l, k, hL):
  +S = Nat.add(U32.to_nat(l), U32.to_nat(k))
  +M = Nat.mul(4n, Nat.pow(2n, 29n))
  +hle = N.lt_to_le(Nat.add(S, 8n), M, hL)
  +h1 = N.le_trans(S, Nat.add(S, 8n), M, N.le_add_r(S, 8n), hle)
  +e1 = C.add_fits(l, k, 29n, {==}, h1)
  +h2 = NM.le_c8(U32.to_nat((l + k : U32)), M, AB.subst(Nat, y => {Nat.is_le(Nat.add(y, 8n), M) == True{} : Bool}, S, U32.to_nat((l + k : U32)), Equal.sym(Nat, U32.to_nat((l + k : U32)), S, e1), hle))
  +e2 = C.add_fits((l + k : U32), 8, 29n, {==}, h2)
  %Equal.sym(Nat, U32.to_nat((l + k + 8 : U32)), Nat.add(U32.to_nat((l + k : U32)), U32.to_nat(8)), e2) : {_ == Nat.add(S, 8n) : Nat}
  %Equal.sym(Nat, U32.to_nat((l + k : U32)), S, e1) : {Nat.add(_, U32.to_nat(8)) == Nat.add(S, 8n) : Nat}
  {==}

# What room gives: a well-formed block (at its tree's depth), the same bytes,
# room for k more.
def RoomP(+l: U32, +t: AT.Tree<U32>, +k: U32, +t2: AT.Tree<U32>) -> Type:
  {D.ok(C.BT(l, t2), RD.tdepth(t2)) == True{} : Bool}
  & ({D.view(C.BT(l, t2)) == D.view(C.BT(l, t)) : List<&2, U32>}
  & {Nat.is_le(Nat.add(U32.to_nat(l), U32.to_nat(k)), D.cap(C.BT(l, t2))) == True{} : Bool})

def room_c(+l: U32, +t: AT.Tree<U32>, +k: U32, +c: Bool,
  hc: {U32.is_le((l + k + 8 : U32), CAPV(l, t)) == c : Bool},
  +hok: {D.ok(C.BT(l, t), RD.tdepth(t)) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(k)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  RoomP(l, t, k, rt.if(c, t, NR.depth(((l + k + 8 : U32) * 2 : U32)))):
  match c:
    case True{}:
      +n = (l + k + 8 : U32)
      +S = Nat.add(U32.to_nat(l), U32.to_nat(k))
      +NN = Nat.add(S, 8n)
      +M = Nat.mul(4n, Nat.pow(2n, 29n))
      +dt = RD.tdepth(t)
      +hn = room_n(l, k, hL)
      +hSn = AB.subst(Nat, y => {Nat.is_le(S, y) == True{} : Bool}, NN, U32.to_nat(n), Equal.sym(Nat, U32.to_nat(n), NN, hn), N.le_add_r(S, 8n))
      +hcv = Equal.trans(Bool, Nat.is_le(U32.to_nat(n), U32.to_nat(CAPV(l, t))), U32.is_le(n, CAPV(l, t)), c,
        Equal.sym(Bool, U32.is_le(n, CAPV(l, t)), Nat.is_le(U32.to_nat(n), U32.to_nat(CAPV(l, t))), U.is_le_to_nat(n, CAPV(l, t))), hc)
      +ecap = O.capacity_view_t(l, t, dt, hok)
      +h3 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(n), y) == True{} : Bool}, U32.to_nat(CAPV(l, t)), D.cap(C.BT(l, t)), ecap, hcv)
      (hok, ({==}, N.le_trans(S, U32.to_nat(n), D.cap(C.BT(l, t)), hSn, h3)))
    case False{}:
      +n = (l + k + 8 : U32)
      +S = Nat.add(U32.to_nat(l), U32.to_nat(k))
      +NN = Nat.add(S, 8n)
      +M = Nat.mul(4n, Nat.pow(2n, 29n))
      +dt = RD.tdepth(t)
      +hn = room_n(l, k, hL)
      +hSn = AB.subst(Nat, y => {Nat.is_le(S, y) == True{} : Bool}, NN, U32.to_nat(n), Equal.sym(Nat, U32.to_nat(n), NN, hn), N.le_add_r(S, 8n))
      +hcv = Equal.trans(Bool, Nat.is_le(U32.to_nat(n), U32.to_nat(CAPV(l, t))), U32.is_le(n, CAPV(l, t)), c,
        Equal.sym(Bool, U32.is_le(n, CAPV(l, t)), Nat.is_le(U32.to_nat(n), U32.to_nat(CAPV(l, t))), U.is_le_to_nat(n, CAPV(l, t))), hc)
      +ecap = O.capacity_view_t(l, t, dt, hok)
      +e = NR.depth((n * 2 : U32))
      +T2 = rt.if(False{}, t, e)
      +hnM = AB.subst(Nat, y => {Nat.is_lt(y, M) == True{} : Bool}, NN, U32.to_nat(n), Equal.sym(Nat, U32.to_nat(n), NN, hn), hL)
      +en2 = NM.mul2_fits(n, hnM)
      +hx1 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(n), y) == True{} : Bool}, Nat.mul(U32.to_nat(n), 2n), U32.to_nat((n * 2 : U32)),
        Equal.sym(Nat, U32.to_nat((n * 2 : U32)), Nat.mul(U32.to_nat(n), 2n), en2), NM.le_dbl(U32.to_nat(n)))
      +hb = NM.depth_bound((n * 2 : U32), U32.to_nat(n), hx1, N.lt_to_le(U32.to_nat(n), M, hnM))
      +hcl = N.not_le_lt(U32.to_nat(n), U32.to_nat(CAPV(l, t)), hcv)
      +ec4 = Equal.trans(Nat, U32.to_nat(CAPV(l, t)), D.cap(C.BT(l, t)), Nat.mul(4n, Nat.pow(2n, dt)), ecap, O.cap_ok_t(l, t, dt, hok))
      +hcl4 = AB.subst(Nat, y => {Nat.is_lt(y, U32.to_nat(n)) == True{} : Bool}, U32.to_nat(CAPV(l, t)), Nat.mul(4n, Nat.pow(2n, dt)), ec4, hcl)
      +hde = NM.pinv(dt, e, N.lt_le_trans(Nat.mul(4n, Nat.pow(2n, dt)), U32.to_nat(n), Nat.mul(4n, Nat.pow(2n, e)), hcl4, hb))
      +he29 = NM.depth_le((n * 2 : U32))
      +ge = G.grow_eq(l, t, dt, e, C.ok_full(l, t, dt, hok))
      +hv = AB.subst(D.Bytes, z => {D.view(z) == D.view(C.BT(l, t)) : List<&2, U32>}, BY.grow(C.BT(l, t), e), C.BT(l, T2), ge,
        G.grow_view_t(l, t, dt, e, hok, hde, he29))
      +hoke = AB.subst(D.Bytes, z => {D.ok(z, e) == True{} : Bool}, BY.grow(C.BT(l, t), e), C.BT(l, T2), ge,
        G.grow_ok_t(l, t, dt, e, hok, hde, he29))
      +hcap = Equal.sym(Nat, D.cap(C.BT(l, T2)), Nat.mul(4n, Nat.pow(2n, e)), O.cap_ok_t(l, T2, e, hoke))
      (LM.ok_td(l, T2, e, hoke), (hv,
        AB.subst(Nat, y => {Nat.is_le(S, y) == True{} : Bool}, Nat.mul(4n, Nat.pow(2n, e)), D.cap(C.BT(l, T2)), hcap,
          N.le_trans(S, U32.to_nat(n), Nat.mul(4n, Nat.pow(2n, e)), hSn, hb))))

def room_p(+l: U32, +t: AT.Tree<U32>, +k: U32, +d: Nat,
  hok: {D.ok(C.BT(l, t), d) == True{} : Bool},
  hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(k)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  RoomP(l, t, k, RT(l, t, k)):
  room_c(l, t, k, U32.is_le((l + k + 8 : U32), CAPV(l, t)), {==}, LM.ok_td(l, t, d, hok), hL)

# Texts and bytes
# ===============

law chars_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {NR.chars(List.append(&2, U32, xs, ys)) == String.append(NR.chars(xs), NR.chars(ys)) : String}

def chars_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %chars_app(t, ys) : {SCon{Chr{x}, NR.chars(List.append(&2, U32, t, ys))} == SCon{Chr{x}, _} : String}
      {==}

law chars_codes:
  for +s: String
  {NR.chars(E.codes(s)) == s : String}

def chars_codes(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %chars_codes(t) : {SCon{Chr{x}, NR.chars(E.codes(t))} == SCon{Chr{x}, _} : String}
      {==}

# put_str
# =======

# The length and the tree put_str.go leaves.
def pstl(s: String, +l: U32) -> U32:
  match s:
    case SNil{}:
      l
    case SCon{c, r}:
      pstl(r, (l + 1 : U32))

def pstt(s: String, +l: U32, +t: AT.Tree<U32>) -> AT.Tree<U32>:
  match s:
    case SNil{}:
      t
    case SCon{Chr{+x}, r}:
      pstt(r, (l + 1 : U32), PA.PT(l, t, x))

law pst_eq:
  for +s: String
  for +l: U32
  for +t: AT.Tree<U32>
  {NR.put_str.go(s, C.BT(l, t)) == C.BT(pstl(s, l), pstt(s, l, t)) : D.Bytes}

def pst_eq(s, l, t):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +r}:
      %Equal.sym(D.Bytes, BY.push(C.BT(l, t), x), C.BT((l + 1 : U32), PA.PT(l, t, x)), O.push_eq_t(l, t, x)) :
        {NR.put_str.go(r, _) == C.BT(pstl(r, (l + 1 : U32)), pstt(r, (l + 1 : U32), PA.PT(l, t, x))) : D.Bytes}
      pst_eq(r, (l + 1 : U32), PA.PT(l, t, x))

law pst_ok:
  for +s: String
  for +l: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hok: {D.ok(C.BT(l, t), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(l), String.length(s)), D.cap(C.BT(l, t))) == True{} : Bool}
  {D.ok(C.BT(pstl(s, l), pstt(s, l, t)), d) == True{} : Bool}

def pst_ok(s, l, t, d, hok, hc):
  match s:
    case SNil{}:
      hok
    case SCon{Chr{+x}, +r}:
      +k = String.length(r)
      pst_ok(r, (l + 1 : U32), PA.PT(l, t, x), d, PA.step_ok(l, t, d, x, k, hok, hc), PA.step_cap(l, t, d, x, k, hok, hc))

law pst_len:
  for +s: String
  for +l: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hok: {D.ok(C.BT(l, t), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(l), String.length(s)), D.cap(C.BT(l, t))) == True{} : Bool}
  {U32.to_nat(pstl(s, l)) == Nat.add(U32.to_nat(l), String.length(s)) : Nat}

def pst_len(s, l, t, d, hok, hc):
  match s:
    case SNil{}:
      Equal.sym(Nat, Nat.add(U32.to_nat(l), 0n), U32.to_nat(l), N.add_zero(U32.to_nat(l)))
    case SCon{Chr{+x}, +r}:
      +k = String.length(r)
      +l1 = (l + 1 : U32)
      +ih = pst_len(r, l1, PA.PT(l, t, x), d, PA.step_ok(l, t, d, x, k, hok, hc), PA.step_cap(l, t, d, x, k, hok, hc))
      +e1 = C.inc_fits(l, d, C.ok_d(l, t, d, hok), PA.step_room(l, t, d, k, hok, hc))
      %Equal.sym(Nat, U32.to_nat(pstl(r, l1)), Nat.add(U32.to_nat(l1), k), ih) : {_ == Nat.add(U32.to_nat(l), 1n+k) : Nat}
      %Equal.sym(Nat, U32.to_nat(l1), Nat.add(U32.to_nat(l), 1n), e1) : {Nat.add(_, k) == Nat.add(U32.to_nat(l), 1n+k) : Nat}
      N.add_assoc(U32.to_nat(l), 1n, k)

law pst_view:
  for +s: String
  for +l: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hok: {D.ok(C.BT(l, t), d) == True{} : Bool}
  for +hb: {E.is_bytes(s) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(l), String.length(s)), D.cap(C.BT(l, t))) == True{} : Bool}
  {D.view(C.BT(pstl(s, l), pstt(s, l, t))) == List.append(&2, U32, D.view(C.BT(l, t)), E.codes(s)) : List<&2, U32>}

def pst_view(s, l, t, d, hok, hb, hc):
  match s:
    case SNil{}:
      Equal.sym(List<&2, U32>, List.append(&2, U32, D.view(C.BT(l, t)), Nil{}), D.view(C.BT(l, t)), PA.append_nil(D.view(C.BT(l, t))))
    case SCon{Chr{+x}, +r}:
      +k = String.length(r)
      +l1 = (l + 1 : U32)
      +T1 = PA.PT(l, t, x)
      +V = D.view(C.BT(l, t))
      +hv = LM.andl(U32.is_lt(x, 256), E.is_bytes(r), hb)
      +hbr = LM.andr(U32.is_lt(x, 256), E.is_bytes(r), hb)
      +ih = pst_view(r, l1, T1, d, PA.step_ok(l, t, d, x, k, hok, hc), hbr, PA.step_cap(l, t, d, x, k, hok, hc))
      +ep = AB.subst(D.Bytes, z => {D.view(z) == List.append(&2, U32, V, [x]) : List<&2, U32>}, BY.push(C.BT(l, t), x), C.BT(l1, T1),
        O.push_eq_t(l, t, x), O.push_view_t(l, t, d, x, hok, PA.step_lt(l, t, d, k, hok, hc), hv))
      %Equal.sym(List<&2, U32>, D.view(C.BT(pstl(r, l1), pstt(r, l1, T1))), List.append(&2, U32, D.view(C.BT(l1, T1)), E.codes(r)), ih) : {_ == List.append(&2, U32, V, x <> E.codes(r)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, D.view(C.BT(l1, T1)), List.append(&2, U32, V, [x]), ep) : {List.append(&2, U32, _, E.codes(r)) == List.append(&2, U32, V, x <> E.codes(r)) : List<&2, U32>}
      PA.append_assoc(V, [x], E.codes(r))

# room's three facts, one at a time.
def rp_ok(+l: U32, +t: AT.Tree<U32>, +k: U32, +t2: AT.Tree<U32>, r: RoomP(l, t, k, t2)) -> {D.ok(C.BT(l, t2), RD.tdepth(t2)) == True{} : Bool}:
  (a, b) = r
  a

def rp_view(+l: U32, +t: AT.Tree<U32>, +k: U32, +t2: AT.Tree<U32>, r: RoomP(l, t, k, t2)) -> {D.view(C.BT(l, t2)) == D.view(C.BT(l, t)) : List<&2, U32>}:
  (a, b) = r
  (v, c) = b
  v

def rp_cap(+l: U32, +t: AT.Tree<U32>, +k: U32, +t2: AT.Tree<U32>, r: RoomP(l, t, k, t2)) -> {Nat.is_le(Nat.add(U32.to_nat(l), U32.to_nat(k)), D.cap(C.BT(l, t2))) == True{} : Bool}:
  (a, b) = r
  (v, c) = b
  c

# put_str on a mirror
# ===================

def SK(+s: String) -> U32:
  U32.from_nat(String.length(s))

# The tree put_str leaves.
def PSR(+l: U32, +t: AT.Tree<U32>, +s: String) -> AT.Tree<U32>:
  pstt(s, l, RT(l, t, SK(s)))

law put_str_eq:
  for +l: U32
  for +t: AT.Tree<U32>
  for +s: String
  for +hf: {A.full(U32, AT.fromT(U32, t), RD.tdepth(t)) == True{} : Bool}
  {NR.put_str(C.BT(l, t), s) == C.BT(pstl(s, l), PSR(l, t, s)) : D.Bytes}

def put_str_eq(l, t, s, hf):
  %Equal.sym(D.Bytes, NR.room(C.BT(l, t), SK(s)), C.BT(l, RT(l, t, SK(s))), room_eq(l, t, SK(s), hf)) :
    {NR.put_str.go(s, _) == C.BT(pstl(s, l), PSR(l, t, s)) : D.Bytes}
  pst_eq(s, l, RT(l, t, SK(s)))

# The text's length as a U32 (it fits).
law sk_nat:
  for +l: U32
  for +s: String
  for +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(s)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {U32.to_nat(SK(s)) == String.length(s) : Nat}

def sk_nat(l, s, hL):
  +L = String.length(s)
  +A = Nat.add(U32.to_nat(l), L)
  +M = Nat.mul(4n, Nat.pow(2n, 29n))
  X.to_nat_fits(L, N.le_trans(L, A, M, N.le_add_l(L, U32.to_nat(l)),
    N.le_trans(A, Nat.add(A, 8n), M, N.le_add_r(A, 8n), N.lt_to_le(Nat.add(A, 8n), M, hL))))

def ps_room(+l: U32, +t: AT.Tree<U32>, +d: Nat, +s: String,
  hok: {D.ok(C.BT(l, t), d) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(s)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  RoomP(l, t, SK(s), RT(l, t, SK(s))):
  room_p(l, t, SK(s), d, hok,
    AB.subst(Nat, y => {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), y), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool},
      String.length(s), U32.to_nat(SK(s)), Equal.sym(Nat, U32.to_nat(SK(s)), String.length(s), sk_nat(l, s, hL)), hL))

def ps_cap(+l: U32, +t: AT.Tree<U32>, +d: Nat, +s: String,
  +hok: {D.ok(C.BT(l, t), d) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(s)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(U32.to_nat(l), String.length(s)), D.cap(C.BT(l, RT(l, t, SK(s))))) == True{} : Bool}:
  AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(l), y), D.cap(C.BT(l, RT(l, t, SK(s))))) == True{} : Bool},
    U32.to_nat(SK(s)), String.length(s), sk_nat(l, s, hL), rp_cap(l, t, SK(s), RT(l, t, SK(s)), ps_room(l, t, d, s, hok, hL)))

law put_str_ok:
  for +l: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: String
  for +hok: {D.ok(C.BT(l, t), d) == True{} : Bool}
  for +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(s)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {D.ok(C.BT(pstl(s, l), PSR(l, t, s)), RD.tdepth(PSR(l, t, s))) == True{} : Bool}

def put_str_ok(l, t, d, s, hok, hL):
  +T2 = RT(l, t, SK(s))
  +okr = rp_ok(l, t, SK(s), T2, ps_room(l, t, d, s, hok, hL))
  LM.ok_td(pstl(s, l), PSR(l, t, s), RD.tdepth(T2), pst_ok(s, l, T2, RD.tdepth(T2), okr, ps_cap(l, t, d, s, hok, hL)))

law put_str_len:
  for +l: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: String
  for +hok: {D.ok(C.BT(l, t), d) == True{} : Bool}
  for +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(s)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {U32.to_nat(pstl(s, l)) == Nat.add(U32.to_nat(l), String.length(s)) : Nat}

def put_str_len(l, t, d, s, hok, hL):
  +T2 = RT(l, t, SK(s))
  pst_len(s, l, T2, RD.tdepth(T2), rp_ok(l, t, SK(s), T2, ps_room(l, t, d, s, hok, hL)), ps_cap(l, t, d, s, hok, hL))

law put_str_text:
  for +l: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: String
  for +hok: {D.ok(C.BT(l, t), d) == True{} : Bool}
  for +hb: {E.is_bytes(s) == True{} : Bool}
  for +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(s)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {NR.chars(D.view(C.BT(pstl(s, l), PSR(l, t, s)))) == String.append(NR.chars(D.view(C.BT(l, t))), s) : String}

def put_str_text(l, t, d, s, hok, hb, hL):
  +T2 = RT(l, t, SK(s))
  +ev = pst_view(s, l, T2, RD.tdepth(T2), rp_ok(l, t, SK(s), T2, ps_room(l, t, d, s, hok, hL)), hb, ps_cap(l, t, d, s, hok, hL))
  +er = rp_view(l, t, SK(s), T2, ps_room(l, t, d, s, hok, hL))
  %Equal.sym(List<&2, U32>, D.view(C.BT(pstl(s, l), PSR(l, t, s))), List.append(&2, U32, D.view(C.BT(l, T2)), E.codes(s)), ev) :
    {NR.chars(_) == String.append(NR.chars(D.view(C.BT(l, t))), s) : String}
  %Equal.sym(List<&2, U32>, D.view(C.BT(l, T2)), D.view(C.BT(l, t)), er) :
    {NR.chars(List.append(&2, U32, _, E.codes(s))) == String.append(NR.chars(D.view(C.BT(l, t))), s) : String}
  %Equal.sym(String, NR.chars(List.append(&2, U32, D.view(C.BT(l, t)), E.codes(s))), String.append(NR.chars(D.view(C.BT(l, t))), NR.chars(E.codes(s))), chars_app(D.view(C.BT(l, t)), E.codes(s))) : {_ == String.append(NR.chars(D.view(C.BT(l, t))), s) : String}
  %Equal.sym(String, NR.chars(E.codes(s)), s, chars_codes(s)) : {String.append(NR.chars(D.view(C.BT(l, t))), _) == String.append(NR.chars(D.view(C.BT(l, t))), s) : String}
  {==}

# A buffer's bytes, all of them.
law view_all:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {D.slice(D.view(C.BT(len, t)), U32.to_nat(0), U32.to_nat(len)) == D.view(C.BT(len, t)) : List<&2, U32>}

def view_all(len, t, d, h):
  +V = D.view(C.BT(len, t))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, PA.drop_zero(V)) : {List.take(&2, U32, _, U32.to_nat(len)) == V : List<&2, U32>}
  %O.view_size_t(len, t, d, h) : {List.take(&2, U32, V, _) == V : List<&2, U32>}
  G.take_all(V)

# reserve
# =======

# The tree reserve leaves.
def RVT(+l: U32, +t: AT.Tree<U32>, +k: U32) -> AT.Tree<U32>:
  rt.if(U32.is_le((l + k + 8 : U32), CAPV(l, t)), t, NR.depth((l + k + 8 : U32)))

law reserve_if:
  for +c: Bool
  for +l: U32
  for +t: AT.Tree<U32>
  for +n: U32
  for +hf: {A.full(U32, AT.fromT(U32, t), RD.tdepth(t)) == True{} : Bool}
  {NR.reserve.if(c, n, C.BT(l, t)) == C.BT(l, rt.if(c, t, NR.depth(n))) : D.Bytes}

def reserve_if(c, l, t, n, hf):
  match c:
    case True{}:
      {==}
    case False{}:
      G.grow_eq(l, t, RD.tdepth(t), NR.depth(n), hf)

law reserve_eq:
  for +l: U32
  for +t: AT.Tree<U32>
  for +k: U32
  for +hf: {A.full(U32, AT.fromT(U32, t), RD.tdepth(t)) == True{} : Bool}
  {NR.reserve.len(k, BY.len(C.BT(l, t))) == C.BT(l, RVT(l, t, k)) : D.Bytes}

def reserve_eq(l, t, k, hf):
  +n = (l + k + 8 : U32)
  %Equal.sym(D.Bytes & U32, BY.capacity(C.BT(l, t)), (C.BT(l, t), CAPV(l, t)), O.capacity_pair_t(l, t)) :
    {NR.reserve.k(n, _) == C.BT(l, RVT(l, t, k)) : D.Bytes}
  reserve_if(U32.is_le(n, CAPV(l, t)), l, t, n, hf)

# What reserve gives: well formed at its tree's depth, the same bytes.
def ResP(+l: U32, +t: AT.Tree<U32>, +t2: AT.Tree<U32>) -> Type:
  {D.ok(C.BT(l, t2), RD.tdepth(t2)) == True{} : Bool}
  & {D.view(C.BT(l, t2)) == D.view(C.BT(l, t)) : List<&2, U32>}

def res_c(+l: U32, +t: AT.Tree<U32>, +k: U32, +c: Bool,
  hc: {U32.is_le((l + k + 8 : U32), CAPV(l, t)) == c : Bool},
  +hok: {D.ok(C.BT(l, t), RD.tdepth(t)) == True{} : Bool}) ->
  ResP(l, t, rt.if(c, t, NR.depth((l + k + 8 : U32)))):
  match c:
    case True{}:
      (hok, {==})
    case False{}:
      +n = (l + k + 8 : U32)
      +dt = RD.tdepth(t)
      +e = NR.depth(n)
      +T2 = rt.if(False{}, t, e)
      +X = Nat.mul(4n, Nat.pow(2n, dt))
      +hcv = Equal.trans(Bool, Nat.is_le(U32.to_nat(n), U32.to_nat(CAPV(l, t))), U32.is_le(n, CAPV(l, t)), False{},
        Equal.sym(Bool, U32.is_le(n, CAPV(l, t)), Nat.is_le(U32.to_nat(n), U32.to_nat(CAPV(l, t))), U.is_le_to_nat(n, CAPV(l, t))), hc)
      +hcl = N.not_le_lt(U32.to_nat(n), U32.to_nat(CAPV(l, t)), hcv)
      +ec4 = Equal.trans(Nat, U32.to_nat(CAPV(l, t)), D.cap(C.BT(l, t)), X, O.capacity_view_t(l, t, dt, hok), O.cap_ok_t(l, t, dt, hok))
      +hx1 = N.lt_to_le(X, U32.to_nat(n), AB.subst(Nat, y => {Nat.is_lt(y, U32.to_nat(n)) == True{} : Bool}, U32.to_nat(CAPV(l, t)), X, ec4, hcl))
      +hx2 = N.le_mul_l(4n, Nat.pow(2n, dt), Nat.pow(2n, 29n), N.pow_le(dt, 29n, C.ok_d(l, t, dt, hok)))
      +hde = NM.pinv_le(dt, e, NM.depth_bound(n, X, hx1, hx2))
      +he29 = NM.depth_le(n)
      +ge = G.grow_eq(l, t, dt, e, C.ok_full(l, t, dt, hok))
      +hv = AB.subst(D.Bytes, z => {D.view(z) == D.view(C.BT(l, t)) : List<&2, U32>}, BY.grow(C.BT(l, t), e), C.BT(l, T2), ge,
        G.grow_view_t(l, t, dt, e, hok, hde, he29))
      +hoke = AB.subst(D.Bytes, z => {D.ok(z, e) == True{} : Bool}, BY.grow(C.BT(l, t), e), C.BT(l, T2), ge,
        G.grow_ok_t(l, t, dt, e, hok, hde, he29))
      (LM.ok_td(l, T2, e, hoke), hv)

def res_p(+l: U32, +t: AT.Tree<U32>, +k: U32,
  hok: {D.ok(C.BT(l, t), RD.tdepth(t)) == True{} : Bool}) -> ResP(l, t, RVT(l, t, k)):
  res_c(l, t, k, U32.is_le((l + k + 8 : U32), CAPV(l, t)), {==}, hok)

def rs_ok(+l: U32, +t: AT.Tree<U32>, +t2: AT.Tree<U32>, r: ResP(l, t, t2)) -> {D.ok(C.BT(l, t2), RD.tdepth(t2)) == True{} : Bool}:
  (a, b) = r
  a

def rs_view(+l: U32, +t: AT.Tree<U32>, +t2: AT.Tree<U32>, r: ResP(l, t, t2)) -> {D.view(C.BT(l, t2)) == D.view(C.BT(l, t)) : List<&2, U32>}:
  (a, b) = r
  b

# Lists
# =====

law len_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}

def len_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %len_app(t, ys) : {1n+List.length(&2, U32, List.append(&2, U32, t, ys)) == 1n+_ : Nat}
      {==}

law drop_len:
  for +xs: List<&2, U32>
  for +s: Nat
  for +n: Nat
  for +h: {Nat.is_le(Nat.add(s, n), List.length(&2, U32, xs)) == True{} : Bool}
  {Nat.is_le(n, List.length(&2, U32, List.drop(&2, U32, xs, s))) == True{} : Bool}

def drop_len(xs, s, n, h):
  match xs s:
    case Nil{} 0n:
      h
    case Nil{} 1n+r:
      Empty.absurd({Nat.is_le(n, 0n) == True{} : Bool}, AB.false_ne_true(h))
    case Con{+x, +t} 0n:
      h
    case Con{+x, +t} 1n+r:
      drop_len(t, r, n, h)

# A slice within the list has its length.
law slice_len:
  for +xs: List<&2, U32>
  for +s: Nat
  for +n: Nat
  for +h: {Nat.is_le(Nat.add(s, n), List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, D.slice(xs, s, n)) == n : Nat}

def slice_len(xs, s, n, h):
  Q.take_length(List.drop(&2, U32, xs, s), n, drop_len(xs, s, n, h))

# put_bytes
# =========

# The buffer F.append leaves (a Bytes; its mirror comes from C.bmirror).
def PBF(+l: U32, +t: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +s: U32, +n: U32) -> D.Bytes:
  Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(l, RT(l, t, n)), C.BT(sl, st), s, n))

def PutB(+l: U32, +t: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +s: U32, +n: U32, +l2: U32, +t2: AT.Tree<U32>) -> Type:
  {NR.put_bytes(C.BT(l, t), C.BT(sl, st), s, n) == (C.BT(l2, t2), C.BT(sl, st)) : D.Bytes & D.Bytes}
  & ({D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool}
  & ({D.view(C.BT(l2, t2)) == List.append(&2, U32, D.view(C.BT(l, t)), D.slice(D.view(C.BT(sl, st)), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}
  & {U32.to_nat(l2) == Nat.add(U32.to_nat(l), U32.to_nat(n)) : Nat}))

def put_bytes.k(+l: U32, +t: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +n: U32,
  +hok: {D.ok(C.BT(l, t), RD.tdepth(t)) == True{} : Bool},
  +hsok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), U32.to_nat(sl)) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(n)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool},
  m: C.BMirror(PBF(l, t, sl, st, s, n))) ->
  &l2: U32 -> &t2: AT.Tree<U32> -> PutB(l, t, sl, st, s, n, l2, t2):
  (+l2, q) = m
  (+t2, e) = q
  +e1 = e
  +T2 = RT(l, t, n)
  +hd = rp_ok(l, t, n, T2, room_p(l, t, n, RD.tdepth(t), hok, hL))
  +hc = rp_cap(l, t, n, T2, room_p(l, t, n, RD.tdepth(t), hok, hL))
  +er = rp_view(l, t, n, T2, room_p(l, t, n, RD.tdepth(t), hok, hL))
  +eap = FE.append_pair(C.BT(l, T2), C.BT(sl, st), s, n)
  +e2 = AB.subst(D.Bytes, z => {F.append(z, C.BT(sl, st), s, n) == (PBF(l, t, sl, st, s, n), C.BT(sl, st)) : D.Bytes & D.Bytes},
    C.BT(l, T2), NR.room(C.BT(l, t), n), Equal.sym(D.Bytes, NR.room(C.BT(l, t), n), C.BT(l, T2), room_eq(l, t, n, C.ok_full(l, t, RD.tdepth(t), hok))), eap)
  +eq = AB.subst(D.Bytes, z => {NR.put_bytes(C.BT(l, t), C.BT(sl, st), s, n) == (z, C.BT(sl, st)) : D.Bytes & D.Bytes},
    PBF(l, t, sl, st, s, n), C.BT(l2, t2), Equal.sym(D.Bytes, C.BT(l2, t2), PBF(l, t, sl, st, s, n), e1), e2)
  +okP = FE.append_ok(C.BT(l, T2), C.BT(sl, st), RD.tdepth(T2), s, n, hd, hc)
  +ok2 = AB.subst(D.Bytes, z => {D.ok(z, RD.tdepth(T2)) == True{} : Bool}, PBF(l, t, sl, st, s, n), C.BT(l2, t2), Equal.sym(D.Bytes, C.BT(l2, t2), PBF(l, t, sl, st, s, n), e1), okP)
  +SL = D.slice(D.view(C.BT(sl, st)), U32.to_nat(s), U32.to_nat(n))
  +vP = FE.append_view(C.BT(l, T2), C.BT(sl, st), RD.tdepth(T2), sd, s, n, hd, hsok, hs, hc)
  +v1 = AB.subst(List<&2, U32>, z => {D.view(PBF(l, t, sl, st, s, n)) == List.append(&2, U32, z, SL) : List<&2, U32>}, D.view(C.BT(l, T2)), D.view(C.BT(l, t)), er, vP)
  +v2 = AB.subst(D.Bytes, z => {D.view(z) == List.append(&2, U32, D.view(C.BT(l, t)), SL) : List<&2, U32>}, PBF(l, t, sl, st, s, n), C.BT(l2, t2), Equal.sym(D.Bytes, C.BT(l2, t2), PBF(l, t, sl, st, s, n), e1), v1)
  +hsl = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), y) == True{} : Bool}, U32.to_nat(sl), List.length(&2, U32, D.view(C.BT(sl, st))),
    Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(sl, st))), U32.to_nat(sl), O.view_size_t(sl, st, sd, hsok)), hs)
  +eln = Equal.trans(Nat, U32.to_nat(l2), List.length(&2, U32, D.view(C.BT(l2, t2))), Nat.add(U32.to_nat(l), U32.to_nat(n)),
    Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(l2, t2))), U32.to_nat(l2), O.view_size_t(l2, t2, RD.tdepth(T2), ok2)),
    Equal.trans(Nat, List.length(&2, U32, D.view(C.BT(l2, t2))), List.length(&2, U32, List.append(&2, U32, D.view(C.BT(l, t)), SL)), Nat.add(U32.to_nat(l), U32.to_nat(n)),
      Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), D.view(C.BT(l2, t2)), List.append(&2, U32, D.view(C.BT(l, t)), SL), v2),
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, D.view(C.BT(l, t)), SL)), Nat.add(List.length(&2, U32, D.view(C.BT(l, t))), List.length(&2, U32, SL)), Nat.add(U32.to_nat(l), U32.to_nat(n)),
        len_app(D.view(C.BT(l, t)), SL),
        Equal.trans(Nat, Nat.add(List.length(&2, U32, D.view(C.BT(l, t))), List.length(&2, U32, SL)), Nat.add(U32.to_nat(l), List.length(&2, U32, SL)), Nat.add(U32.to_nat(l), U32.to_nat(n)),
          Equal.cong(Nat, Nat, z => Nat.add(z, List.length(&2, U32, SL)), List.length(&2, U32, D.view(C.BT(l, t))), U32.to_nat(l), O.view_size_t(l, t, RD.tdepth(t), hok)),
          Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(l), z), List.length(&2, U32, SL), U32.to_nat(n), slice_len(D.view(C.BT(sl, st)), U32.to_nat(s), U32.to_nat(n), hsl))))))
  (l2, (t2, (eq, (LM.ok_td(l2, t2, RD.tdepth(T2), ok2), (v2, eln)))))

def put_bytes_t(+l: U32, +t: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +n: U32,
  +hok: {D.ok(C.BT(l, t), RD.tdepth(t)) == True{} : Bool},
  +hsok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), U32.to_nat(sl)) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(n)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  &l2: U32 -> &t2: AT.Tree<U32> -> PutB(l, t, sl, st, s, n, l2, t2):
  put_bytes.k(l, t, sl, st, sd, s, n, hok, hsok, hs, hL, C.bmirror(PBF(l, t, sl, st, s, n)))

# An empty buffer holds nothing.
law view0:
  for +t: AT.Tree<U32>
  {D.view(C.BT(0, t)) == Nil{} : List<&2, U32>}

def view0(t):
  Q.take_zero(D.unpack(A.view(U32, AT.fromT(U32, t))))

law str_take0:
  for +s: String
  {String.take(s, 0n) == "" : String}

def str_take0(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      {==}

law str_drop0:
  for +s: String
  {String.drop(s, 0n) == s : String}

def str_drop0(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      {==}

law chars_take:
  for +xs: List<&2, U32>
  for +n: Nat
  {NR.chars(List.take(&2, U32, xs, n)) == String.take(NR.chars(xs), n) : String}

def chars_take(xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+m:
      %chars_take(t, m) : {SCon{Chr{x}, NR.chars(List.take(&2, U32, t, m))} == SCon{Chr{x}, _} : String}
      {==}

law chars_drop:
  for +xs: List<&2, U32>
  for +n: Nat
  {NR.chars(List.drop(&2, U32, xs, n)) == String.drop(NR.chars(xs), n) : String}

def chars_drop(xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+m:
      chars_drop(t, m)

law drop_length:
  for +xs: List<&2, U32>
  for +a: Nat
  {List.length(&2, U32, List.drop(&2, U32, xs, a)) == Nat.sub(List.length(&2, U32, xs), a) : Nat}

def drop_length(xs, a):
  match xs a:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+m:
      drop_length(t, m)

# The bytes from a on.
law slice_rest:
  for +xs: List<&2, U32>
  for +a: Nat
  {D.slice(xs, a, Nat.sub(List.length(&2, U32, xs), a)) == List.drop(&2, U32, xs, a) : List<&2, U32>}

def slice_rest(xs, a):
  %drop_length(xs, a) :
    {List.take(&2, U32, List.drop(&2, U32, xs, a), _) == List.drop(&2, U32, xs, a) : List<&2, U32>}
  G.take_all(List.drop(&2, U32, xs, a))

law tnew_td:
  for +d: Nat
  for +v: U32
  {RD.tdepth(G.tnew(d, v)) == d : Nat}

def tnew_td(d, v):
  match d:
    case 0n:
      {==}
    case 1n+p:
      %tnew_td(p, v) : {1n+RD.tdepth(G.tnew(p, v)) == 1n+_ : Nat}
      {==}

# A new block of depth d <= 29 as a well-formed empty buffer.
law empty_ok_td:
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  {D.ok(C.BT(0, G.tnew(d, 0)), RD.tdepth(G.tnew(d, 0))) == True{} : Bool}

def empty_ok_td(d, hd):
  LM.ok_td(0, G.tnew(d, 0), d, C.ok_mk(0, G.tnew(d, 0), d, G.tnew_full(d, 0), hd, I.le0(Nat.mul(4n, Nat.pow(2n, d)))))

law str_take_add:
  for +s: String
  for +a: Nat
  for +b: Nat
  {String.take(s, Nat.add(a, b)) == String.append(String.take(s, a), String.take(String.drop(s, a), b)) : String}

def str_take_add(s, a, b):
  match s a:
    case SNil{} _:
      {==}
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+m:
      %str_take_add(t, m, b) : {SCon{c, String.take(t, Nat.add(m, b))} == SCon{c, _} : String}
      {==}

law str_drop_add:
  for +s: String
  for +a: Nat
  for +b: Nat
  {String.drop(s, Nat.add(a, b)) == String.drop(String.drop(s, a), b) : String}

def str_drop_add(s, a, b):
  match s a:
    case SNil{} _:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+m:
      str_drop_add(t, m, b)

# Reversing onto a non-empty list gives a non-empty list.
def rev_nz(xs: List<&2, NR.Ck>, +y: NR.Ck, +acc: List<&2, NR.Ck>) ->
  &z: NR.Ck -> &zs: List<&2, NR.Ck> -> {NR.rev_ck(xs, Con{y, acc}) == Con{z, zs} : List<&2, NR.Ck>}:
  match xs:
    case Nil{}:
      (y, (acc, {==}))
    case Con{+x, +t}:
      rev_nz(t, x, Con{y, acc})
