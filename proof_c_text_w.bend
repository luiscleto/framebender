import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fix.bend as NX
import ./bytes_enc.bend as E
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_sz.bend as SZ
import ./proof_b_lit.bend as PL
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_index.bend as I
import lawful-words@0.1.0.0/defs.bend as W

# Phase C: norm_fix.bend's writes into the rewritten line's buffer (put_b,
# put_s, put_c), on mirrors: each hands the line and the window back, and
# when its size check passes it appends its piece. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def V(+l: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(l, t))

def OK(+l: U32, +t: AT.Tree<U32>) -> Bool:
  D.ok(C.BT(l, t), RD.tdepth(t))

# ---------------------------------------------------------------------------
# Sizes: the checks keep a write within 2^31 bytes
# ---------------------------------------------------------------------------

# x, y <= 2^B give x + y <= 2^(1+B) (B kept a variable).
law sum_le:
  for +x: Nat
  for +y: Nat
  for +Bx: Nat
  for +e: Nat
  for +he: {1n+Bx == e : Nat}
  for +hx: {Nat.is_le(x, Nat.pow(2n, Bx)) == True{} : Bool}
  for +hy: {Nat.is_le(y, Nat.pow(2n, Bx)) == True{} : Bool}
  {Nat.is_le(Nat.add(x, y), Nat.pow(2n, e)) == True{} : Bool}

def sum_le(x, y, Bx, e, he, hx, hy):
  +P = Nat.pow(2n, Bx)
  +h1 = N.le_trans(Nat.add(x, y), Nat.add(P, y), Nat.add(P, P), N.le_add_mono_r(y, x, P, hx), N.le_add_mono_l(P, y, P, hy))
  %he : {Nat.is_le(Nat.add(x, y), Nat.pow(2n, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(P, 0n), P, N.add_zero(P)) : {Nat.is_le(Nat.add(x, y), Nat.add(P, _)) == True{} : Bool}
  h1

# A word at most 2^29 and one at most 2^28: their sum and 8 stay below 2^31.
def hl29(+l: U32, +k: Nat,
  +hl: {U32.is_le(l, 536870912) == True{} : Bool},
  +hk: {Nat.is_le(k, Nat.pow(2n, 28n)) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), k), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}:
  +h1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(l), U32.to_nat(536870912)), U32.is_le(l, 536870912), True{}, Equal.sym(Bool, U32.is_le(l, 536870912), Nat.is_le(U32.to_nat(l), U32.to_nat(536870912)), U.is_le_to_nat(l, 536870912)), hl)
  +h2 = AB.subst(Nat, z => {Nat.is_le(U32.to_nat(l), z) == True{} : Bool}, U32.to_nat(536870912), Nat.pow(2n, 29n), PL.lit_pow(29n, 536870912, {==}, {==}), h1)
  +hk2 = N.le_trans(k, Nat.pow(2n, 28n), Nat.pow(2n, 29n), hk, N.pow_le(28n, 29n, {==}))
  SZ.lt31(Nat.add(U32.to_nat(l), k), sum_le(U32.to_nat(l), k, 29n, 30n, {==}, h2, hk2))

def wk28(+k: U32, +hk: {U32.is_le(k, 268435456) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(k), Nat.pow(2n, 28n)) == True{} : Bool}:
  +h1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(k), U32.to_nat(268435456)), U32.is_le(k, 268435456), True{}, Equal.sym(Bool, U32.is_le(k, 268435456), Nat.is_le(U32.to_nat(k), U32.to_nat(268435456)), U.is_le_to_nat(k, 268435456)), hk)
  AB.subst(Nat, z => {Nat.is_le(U32.to_nat(k), z) == True{} : Bool}, U32.to_nat(268435456), Nat.pow(2n, 28n), PL.lit28w(), h1)

def hl29w(+l: U32, +k: U32,
  +hl: {U32.is_le(l, 536870912) == True{} : Bool},
  +hk: {U32.is_le(k, 268435456) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(k)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}:
  hl29(l, U32.to_nat(k), hl, wk28(k, hk))

# NX.len_le is norm.bend's len_le.
law lle_go:
  for +s: String
  for +z: Bool
  for +w: U32
  {NX.len_le.go(s, z, w) == Norm.len_le.go(s, z, w) : Bool}

def lle_go(s, z, w):
  match s z:
    case SNil{} _:
      {==}
    case SCon{+h, +t} True{}:
      {==}
    case SCon{+h, +t} False{}:
      lle_go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32))

def lle(+s: String, +w: U32) -> {NX.len_le(s, w) == Norm.len_le(s, w) : Bool}:
  lle_go(s, U32.is_zero(w), w)

# ---------------------------------------------------------------------------
# The writes, when their check passes
# ---------------------------------------------------------------------------

def WbG(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, r: NX.Wb, +l: U32, +t: AT.Tree<U32>, +pc: List<&2, U32>) -> Type:
  &l2: U32 -> &t2: AT.Tree<U32> -> ({r == NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}} : NX.Wb}
  & ({OK(l2, t2) == True{} : Bool}
  & {V(l2, t2) == List.append(&2, U32, V(l, t), pc) : List<&2, U32>}))

def PBC(+l: U32, +k: U32) -> Bool:
  Bool.and(U32.is_le(l, 536870912), U32.is_le(k, 268435456))

def pbt.k(+l: U32, +t: AT.Tree<U32>, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +s: U32, +k: U32,
  +hok: {OK(l, t) == True{} : Bool},
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool},
  m: &l2: U32 -> &t2: AT.Tree<U32> -> BF.PutB(l, t, bl, bt, s, k, l2, t2)) ->
  WbG(bl, bt, wl, wt, NX.pb.ok(True{}, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), s, k), l, t, D.slice(V(bl, bt), U32.to_nat(s), U32.to_nat(k))):
  (+l2, q) = m
  (+t2, pb) = q
  (eq, r1) = pb
  (okd, r2) = r1
  (vw, ln) = r2
  %Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(l, t), C.BT(bl, bt), s, k), (C.BT(l2, t2), C.BT(bl, bt)), eq) :
    WbG(bl, bt, wl, wt, NX.pb.fin(C.BT(wl, wt), _), l, t, D.slice(V(bl, bt), U32.to_nat(s), U32.to_nat(k)))
  (l2, (t2, ({==}, (okd, vw))))

# Bytes s .. s+k-1 of the line.
def put_b_t(+l: U32, +t: AT.Tree<U32>, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +s: U32, +k: U32,
  +hok: {OK(l, t) == True{} : Bool},
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool},
  +hg: {PBC(l, k) == True{} : Bool}) ->
  WbG(bl, bt, wl, wt, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, s, k), l, t, D.slice(V(bl, bt), U32.to_nat(s), U32.to_nat(k))):
  +hL = hl29(l, U32.to_nat(k), N.and_true_l(U32.is_le(l, 536870912), U32.is_le(k, 268435456), hg), wk28(k, N.and_true_r(U32.is_le(l, 536870912), U32.is_le(k, 268435456), hg)))
  %Equal.sym(Bool, PBC(l, k), True{}, hg) :
    WbG(bl, bt, wl, wt, NX.pb.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), s, k), l, t, D.slice(V(bl, bt), U32.to_nat(s), U32.to_nat(k)))
  pbt.k(l, t, bl, bt, bd, wl, wt, s, k, hok, hbo, hs, BF.put_bytes_t(l, t, bl, bt, bd, s, k, hok, hbo, hs, hL))

# A text (its bytes, one per Char).
def put_s_t(+l: U32, +t: AT.Tree<U32>, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +str: String,
  +hok: {OK(l, t) == True{} : Bool},
  +hb: {E.is_bytes(str) == True{} : Bool},
  +hg: {Bool.and(U32.is_le(l, 536870912), NX.len_le(str, 268435456)) == True{} : Bool}) ->
  &l2: U32 -> &t2: AT.Tree<U32> -> ({NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, str) == NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}} : NX.Wb}
  & ({OK(l2, t2) == True{} : Bool}
  & {NR.chars(V(l2, t2)) == String.append(NR.chars(V(l, t)), str) : String})):
  +hl = N.and_true_l(U32.is_le(l, 536870912), NX.len_le(str, 268435456), hg)
  +hs0 = N.and_true_r(U32.is_le(l, 536870912), NX.len_le(str, 268435456), hg)
  +hs1 = Equal.trans(Bool, Norm.len_le(str, 268435456), NX.len_le(str, 268435456), True{}, Equal.sym(Bool, NX.len_le(str, 268435456), Norm.len_le(str, 268435456), lle(str, 268435456)), hs0)
  +hL = hl29(l, String.length(str), hl, SZ.len28(str, hs1))
  +d = RD.tdepth(t)
  %Equal.sym(Bool, Bool.and(U32.is_le(l, 536870912), NX.len_le(str, 268435456)), True{}, hg) :
    &l2: U32 -> &t2: AT.Tree<U32> -> ({NX.ps.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), str) == NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}} : NX.Wb}
    & ({OK(l2, t2) == True{} : Bool}
    & {NR.chars(V(l2, t2)) == String.append(NR.chars(V(l, t)), str) : String}))
  %Equal.sym(D.Bytes, NR.put_str(C.BT(l, t), str), C.BT(BF.pstl(str, l), BF.PSR(l, t, str)), BF.put_str_eq(l, t, str, C.ok_full(l, t, d, hok))) :
    &l2: U32 -> &t2: AT.Tree<U32> -> ({NX.Wb{_, C.BT(bl, bt), C.BT(wl, wt), True{}} == NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}} : NX.Wb}
    & ({OK(l2, t2) == True{} : Bool}
    & {NR.chars(V(l2, t2)) == String.append(NR.chars(V(l, t)), str) : String}))
  (BF.pstl(str, l), (BF.PSR(l, t, str), ({==}, (BF.put_str_ok(l, t, d, str, hok, hL), BF.put_str_text(l, t, d, str, hok, hb, hL)))))

def pct.k(+l: U32, +t: AT.Tree<U32>, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +x: U32,
  +hok: {OK(l, t) == True{} : Bool},
  +hx: {U32.is_lt(x, 256) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), U32.to_nat(1)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  WbG(bl, bt, wl, wt, NX.Wb{BY.push(NR.room(C.BT(l, t), 1), x), C.BT(bl, bt), C.BT(wl, wt), True{}}, l, t, [x]):
  +T2 = BF.RT(l, t, 1)
  +ok2 = BF.rp_ok(l, t, 1, T2, BF.room_p(l, t, 1, RD.tdepth(t), hok, hL))
  +hcap = BF.rp_cap(l, t, 1, T2, BF.room_p(l, t, 1, RD.tdepth(t), hok, hL))
  +hc = {%N.le_succ_lt(U32.to_nat(l), D.cap(C.BT(l, T2))) : {_ == True{} : Bool};
    %N.add_one(U32.to_nat(l)) : {Nat.is_le(_, D.cap(C.BT(l, T2))) == True{} : Bool};
    hcap : {Nat.is_lt(U32.to_nat(l), D.cap(C.BT(l, T2))) == True{} : Bool}}
  +ept = O.push_eq_t(l, T2, x)
  +L2 = (l + 1 : U32)
  +t2 = I.set_tree(U32, T2, (l >> 2n : U32), W.put_byte(C.WD(T2, (l >> 2n : U32)), U32.to_nat((l .&. 3 : U32)), x))
  +okp = AB.subst(D.Bytes, z => {D.ok(z, RD.tdepth(T2)) == True{} : Bool}, BY.push(C.BT(l, T2), x), C.BT(L2, t2), ept, O.push_ok_t(l, T2, RD.tdepth(T2), x, ok2, hc))
  +vp = AB.subst(D.Bytes, z => {D.view(z) == List.append(&2, U32, V(l, T2), [x]) : List<&2, U32>}, BY.push(C.BT(l, T2), x), C.BT(L2, t2), ept, O.push_view_t(l, T2, RD.tdepth(T2), x, ok2, hc, hx))
  +vp2 = AB.subst(List<&2, U32>, z => {D.view(C.BT(L2, t2)) == List.append(&2, U32, z, [x]) : List<&2, U32>}, V(l, T2), V(l, t), BF.rp_view(l, t, 1, T2, BF.room_p(l, t, 1, RD.tdepth(t), hok, hL)), vp)
  %Equal.sym(D.Bytes, NR.room(C.BT(l, t), 1), C.BT(l, T2), BF.room_eq(l, t, 1, C.ok_full(l, t, RD.tdepth(t), hok))) :
    WbG(bl, bt, wl, wt, NX.Wb{BY.push(_, x), C.BT(bl, bt), C.BT(wl, wt), True{}}, l, t, [x])
  %Equal.sym(D.Bytes, BY.push(C.BT(l, T2), x), C.BT(L2, t2), ept) :
    WbG(bl, bt, wl, wt, NX.Wb{_, C.BT(bl, bt), C.BT(wl, wt), True{}}, l, t, [x])
  (L2, (t2, ({==}, (LM.ok_td(L2, t2, RD.tdepth(T2), okp), vp2))))

# One byte x (x < 256).
def put_c_t(+l: U32, +t: AT.Tree<U32>, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +x: U32,
  +hok: {OK(l, t) == True{} : Bool},
  +hx: {U32.is_lt(x, 256) == True{} : Bool},
  +hg: {Bool.and(U32.is_le(l, 536870912), U32.is_le(1, 268435456)) == True{} : Bool}) ->
  WbG(bl, bt, wl, wt, NX.put_c(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, x), l, t, [x]):
  %Equal.sym(Bool, Bool.and(U32.is_le(l, 536870912), U32.is_le(1, 268435456)), True{}, hg) :
    WbG(bl, bt, wl, wt, NX.pc.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), x), l, t, [x])
  pct.k(l, t, bl, bt, wl, wt, x, hok, hx, hl29w(l, 1, N.and_true_l(U32.is_le(l, 536870912), U32.is_le(1, 268435456), hg), {==}))
