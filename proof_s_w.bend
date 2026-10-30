import Base
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_lem.bend as LM
import ./proof_c_text_w.bend as TW
import ./proof_b_adv_nat.bend as LP
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_index.bend as I
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The byte splitter's writer (norm_split.bend's Sw) on mirrors: the line is
# C.BT(len, t), the records written so far a mirror whose view is a list.
# Each write is mirrored by a function on Data (Wm: the list written, the
# range not copied yet, the flag); Rel says a writer state is the mirror of
# a model state. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def V(+l: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(l, t))

def OK(+l: U32, +t: AT.Tree<U32>) -> Bool:
  D.ok(C.BT(l, t), RD.tdepth(t))

def Us() -> Data:
  List<&2, U32>

# ---------------------------------------------------------------------------
# The model
# ---------------------------------------------------------------------------

type Wm is Data:
  Wm{out: List<&2, U32>, p: NS.Rg, ok: Bool}

def Wm.ok(m: Wm) -> Bool:
  match m:
    case Wm{out, p, ok}:
      ok

def LN(+out: List<&2, U32>) -> U32:
  U32.from_nat(List.length(&2, U32, out))

# Bytes a .. z-1 of the line.
def SL(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> List<&2, U32>:
  D.slice(V(len, t), n(a), n((z - a : U32)))

def Wm.flush.ok(ok: Bool, +len: U32, +t: AT.Tree<U32>, +out: List<&2, U32>, +a: U32, +z: U32) -> Wm:
  match ok:
    case True{}:
      Wm{List.append(&2, U32, out, SL(len, t, a, z)), NS.Rg{z, z}, True{}}
    case False{}:
      Wm{out, NS.Rg{a, z}, False{}}

def Wm.flush.if(empty: Bool, +len: U32, +t: AT.Tree<U32>, +out: List<&2, U32>, +a: U32, +z: U32) -> Wm:
  match empty:
    case True{}:
      Wm{out, NS.Rg{a, z}, True{}}
    case False{}:
      Wm.flush.ok(U32.is_le(LN(out), 536870912) && U32.is_le((z - a : U32), 268435456), len, t, out, a, z)

def Wm.flush(+len: U32, +t: AT.Tree<U32>, m: Wm) -> Wm:
  match m:
    case Wm{+out, NS.Rg{+a, +z}, True{}}:
      Wm.flush.if(U32.is_le(z, a), len, t, out, a, z)
    case Wm{out, p, False{}}:
      Wm{out, p, False{}}

def Wm.with_p(m: Wm, +x: NS.Rg) -> Wm:
  match m:
    case Wm{out, p, ok}:
      Wm{out, x, ok}

def Wm.fail(m: Wm) -> Wm:
  match m:
    case Wm{out, p, ok}:
      Wm{out, p, False{}}

def Wm.cpr.if(next: Bool, +len: U32, +t: AT.Tree<U32>, m: Wm, +a: U32, +x: NS.Rg) -> Wm:
  match next:
    case True{}:
      Wm.with_p(m, NS.Rg{a, NS.Rg.z(x)})
    case False{}:
      Wm.with_p(Wm.flush(len, t, m), x)

def Wm.cpr(+len: U32, +t: AT.Tree<U32>, m: Wm, +x: NS.Rg) -> Wm:
  match m:
    case Wm{+out, NS.Rg{+a, +z}, True{}}:
      Wm.cpr.if(U32.is_eq(NS.Rg.a(x), z), len, t, Wm{out, NS.Rg{a, z}, True{}}, a, x)
    case Wm{out, p, False{}}:
      Wm{out, p, False{}}

def Wm.push.ok(ok: Bool, +out: List<&2, U32>, +z: U32, +x: U32) -> Wm:
  match ok:
    case True{}:
      Wm{List.append(&2, U32, out, [x]), NS.Rg{z, z}, True{}}
    case False{}:
      Wm{out, NS.Rg{z, z}, False{}}

def Wm.push(m: Wm, +x: U32) -> Wm:
  match m:
    case Wm{+out, NS.Rg{a, +z}, True{}}:
      Wm.push.ok(U32.is_le(LN(out), 536870912) && U32.is_le(1, 268435456), out, z, x)
    case Wm{out, p, False{}}:
      Wm{out, p, False{}}

def Wm.ch.if(same: Bool, +len: U32, +t: AT.Tree<U32>, +out: List<&2, U32>, +a: U32, +z: U32, +x: U32) -> Wm:
  match same:
    case True{}:
      Wm{out, NS.Rg{a, (z + 1 : U32)}, True{}}
    case False{}:
      Wm.push(Wm.flush(len, t, Wm{out, NS.Rg{a, z}, True{}}), x)

def Wm.ch.in(inside: Bool, +len: U32, +t: AT.Tree<U32>, +out: List<&2, U32>, +a: U32, +z: U32, +x: U32) -> Wm:
  match inside:
    case True{}:
      Wm.ch.if(U32.is_eq(C.AT(len, t, z), x), len, t, out, a, z, x)
    case False{}:
      Wm.push(Wm.flush(len, t, Wm{out, NS.Rg{a, z}, True{}}), x)

def Wm.ch(+len: U32, +t: AT.Tree<U32>, m: Wm, +x: U32) -> Wm:
  match m:
    case Wm{+out, NS.Rg{+a, +z}, True{}}:
      Wm.ch.in(U32.is_lt(z, len), len, t, out, a, z, x)
    case Wm{out, p, False{}}:
      Wm{out, p, False{}}

def Wm.sep(+len: U32, +t: AT.Tree<U32>, m: Wm, first: Bool, +x: U32) -> Wm:
  match first:
    case True{}:
      m
    case False{}:
      Wm.ch(len, t, m, x)

# ---------------------------------------------------------------------------
# The relation
# ---------------------------------------------------------------------------

# The range not copied yet is within the line.
def PV(+len: U32, +p: NS.Rg) -> Bool:
  match p:
    case NS.Rg{+a, +z}:
      Nat.is_le(n(a), n(z)) && Nat.is_le(n(z), n(len))

def Rel(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m: Wm) -> Type:
  match m:
    case Wm{+out, +p, +ok}:
      &l2: U32 -> &t2: AT.Tree<U32> -> ({w == NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok} : NS.Sw}
        & ({OK(l2, t2) == True{} : Bool} & ({V(l2, t2) == out : List<&2, U32>} & {PV(len, p) == True{} : Bool})))

# A write F mirrored by Fm, from any state with the range within the line.
def Op(+len: U32, +t: AT.Tree<U32>, -F: NS.Sw -> NS.Sw, -Fm: Wm -> Wm) -> Type:
  @+l2: U32 -> @+t2: AT.Tree<U32> -> @+p: NS.Rg -> @+ok: Bool -> @+h: {OK(l2, t2) == True{} : Bool} -> @+hp: {PV(len, p) == True{} : Bool} ->
    Rel(len, t, F(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}), Fm(Wm{V(l2, t2), p, ok}))

def bind(+len: U32, +t: AT.Tree<U32>, -F: NS.Sw -> NS.Sw, -Fm: Wm -> Wm, f: Op(len, t, F, Fm), -w: NS.Sw, +m: Wm, r: Rel(len, t, w, m)) -> Rel(len, t, F(w), Fm(m)):
  match m:
    case Wm{+out, +p, +ok}:
      (+l2, q) = r
      (+t2, e) = q
      (eq, r1) = e
      (hok, r2) = r1
      (hv, hp) = r2
      %Equal.sym(NS.Sw, w, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, eq) : Rel(len, t, F(_), Fm(Wm{out, p, ok}))
      %hv : Rel(len, t, F(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}), Fm(Wm{_, p, ok}))
      f(l2, t2, p, ok, hok, hp)

# A state is its own mirror.
def refl(+len: U32, +l2: U32, +t: AT.Tree<U32>, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, p) == True{} : Bool}) ->
  Rel(len, t, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, Wm{V(l2, t2), p, ok}):
  (l2, (t2, ({==}, (h, ({==}, hp)))))

# ---------------------------------------------------------------------------
# Small facts
# ---------------------------------------------------------------------------

def ln_eq(+l: U32, +t: AT.Tree<U32>, +h: {OK(l, t) == True{} : Bool}) -> {LN(V(l, t)) == l : U32}:
  %Equal.sym(Nat, List.length(&2, U32, V(l, t)), n(l), O.view_size_t(l, t, RD.tdepth(t), h)) : {U32.from_nat(_) == l : U32}
  U.from_nat_to_nat(l)

def pv_a(+len: U32, +a: U32, +z: U32, +h: {PV(len, NS.Rg{a, z}) == True{} : Bool}) -> {Nat.is_le(n(a), n(z)) == True{} : Bool}:
  N.and_true_l(Nat.is_le(n(a), n(z)), Nat.is_le(n(z), n(len)), h)

def pv_z(+len: U32, +a: U32, +z: U32, +h: {PV(len, NS.Rg{a, z}) == True{} : Bool}) -> {Nat.is_le(n(z), n(len)) == True{} : Bool}:
  N.and_true_r(Nat.is_le(n(a), n(z)), Nat.is_le(n(z), n(len)), h)

def pv_mk(+len: U32, +a: U32, +z: U32, +ha: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool}) -> {PV(len, NS.Rg{a, z}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(n(a), n(z)), True{}, ha) : {Bool.and(_, Nat.is_le(n(z), n(len))) == True{} : Bool}
  hz

def pv_zz(+len: U32, +a: U32, +z: U32, +h: {PV(len, NS.Rg{a, z}) == True{} : Bool}) -> {PV(len, NS.Rg{z, z}) == True{} : Bool}:
  pv_mk(len, z, z, N.le_refl(n(z)), pv_z(len, a, z, h))

# n(z - a) == n(z) - n(a) for a <= z.
def nsub(+a: U32, +z: U32, +h: {Nat.is_le(n(a), n(z)) == True{} : Bool}) -> {n((z - a : U32)) == Nat.sub(n(z), n(a)) : Nat}:
  U.to_nat_sub_le(z, a, Equal.trans(Bool, U32.is_le(a, z), Nat.is_le(n(a), n(z)), True{}, U.is_le_to_nat(a, z), h))

# a + (z - a) <= len.
def pv_put(+len: U32, +a: U32, +z: U32, +h: {PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n(a), n((z - a : U32))), n(len)) == True{} : Bool}:
  %Equal.sym(Nat, n((z - a : U32)), Nat.sub(n(z), n(a)), nsub(a, z, pv_a(len, a, z, h))) : {Nat.is_le(Nat.add(n(a), _), n(len)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n(a), Nat.sub(n(z), n(a))), n(z), N.le_sub_add(n(a), n(z), pv_a(len, a, z, h))) : {Nat.is_le(_, n(len)) == True{} : Bool}
  pv_z(len, a, z, h)

# z < len: z + 1 does not wrap, and a <= z gives a .. z+1 within the line.
def inc_n(+len: U32, +t: AT.Tree<U32>, +d: Nat, +z: U32, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +h: {U32.is_lt(z, len) == True{} : Bool}) ->
  {n((z + 1 : U32)) == Nat.add(n(z), 1n) : Nat}:
  LP.inc_len(len, t, d, z, hl, Equal.trans(Bool, Nat.is_lt(n(z), n(len)), U32.is_lt(z, len), True{}, Equal.sym(Bool, U32.is_lt(z, len), Nat.is_lt(n(z), n(len)), U.is_lt_to_nat(z, len)), h))

def pv_inc(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool}, +h: {U32.is_lt(z, len) == True{} : Bool}) -> {PV(len, NS.Rg{a, (z + 1 : U32)}) == True{} : Bool}:
  +hz = Equal.trans(Bool, Nat.is_lt(n(z), n(len)), U32.is_lt(z, len), True{}, Equal.sym(Bool, U32.is_lt(z, len), Nat.is_lt(n(z), n(len)), U.is_lt_to_nat(z, len)), h)
  +e = Equal.sym(Nat, n((z + 1 : U32)), Nat.add(n(z), 1n), inc_n(len, t, d, z, hl, h))
  +ha = {%e : {Nat.is_le(n(a), _) == True{} : Bool}; N.le_trans(n(a), n(z), Nat.add(n(z), 1n), pv_a(len, a, z, hp), N.le_add_r(n(z), 1n)) : {Nat.is_le(n(a), n((z + 1 : U32))) == True{} : Bool}}
  +hb = {%e : {Nat.is_le(_, n(len)) == True{} : Bool}; %Equal.sym(Nat, Nat.add(n(z), 1n), 1n+n(z), N.add_one(n(z))) : {Nat.is_le(_, n(len)) == True{} : Bool}; %Equal.sym(Bool, Nat.is_le(1n+n(z), n(len)), Nat.is_lt(n(z), n(len)), N.le_succ_lt(n(z), n(len))) : {_ == True{} : Bool}; hz : {Nat.is_le(n((z + 1 : U32)), n(len)) == True{} : Bool}}
  pv_mk(len, a, (z + 1 : U32), ha, hb)

# ---------------------------------------------------------------------------
# The writes on mirrors
# ---------------------------------------------------------------------------

def flush_put.k(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32,
  +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool},
  m: &l3: U32 -> &t3: AT.Tree<U32> -> BF.PutB(l2, t2, len, t, a, (z - a : U32), l3, t3)) ->
  Rel(len, t, NS.flush.ok(True{}, C.BT(len, t), C.BT(l2, t2), a, z), Wm.flush.ok(True{}, len, t, V(l2, t2), a, z)):
  (+l3, q) = m
  (+t3, pb) = q
  (eq, r1) = pb
  (okd, r2) = r1
  (vw, ln) = r2
  %Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(l2, t2), C.BT(len, t), a, (z - a : U32)), (C.BT(l3, t3), C.BT(len, t)), eq) :
    Rel(len, t, NS.flush.fin(_, z), Wm{List.append(&2, U32, V(l2, t2), SL(len, t, a, z)), NS.Rg{z, z}, True{}})
  (l3, (t3, ({==}, (okd, (vw, pv_zz(len, a, z, hp))))))

def flush_ok(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(l2, 536870912), U32.is_le((z - a : U32), 268435456)) == c : Bool}) ->
  Rel(len, t, NS.flush.ok(c, C.BT(len, t), C.BT(l2, t2), a, z), Wm.flush.ok(c, len, t, V(l2, t2), a, z)):
  match c:
    case True{}:
      +hL = TW.hl29w(l2, (z - a : U32), N.and_true_l(U32.is_le(l2, 536870912), U32.is_le((z - a : U32), 268435456), hc), N.and_true_r(U32.is_le(l2, 536870912), U32.is_le((z - a : U32), 268435456), hc))
      flush_put.k(len, t, l2, t2, a, z, hp, BF.put_bytes_t(l2, t2, len, t, d, a, (z - a : U32), h, hl, pv_put(len, a, z, hp), hL))
    case False{}:
      refl(len, l2, t, t2, NS.Rg{a, z}, False{}, h, hp)

def flush_if(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  Rel(len, t, NS.flush.if(c, C.BT(len, t), C.BT(l2, t2), a, z), Wm.flush.if(c, len, t, V(l2, t2), a, z)):
  match c:
    case True{}:
      refl(len, l2, t, t2, NS.Rg{a, z}, True{}, h, hp)
    case False{}:
      %Equal.sym(U32, LN(V(l2, t2)), l2, ln_eq(l2, t2, h)) :
        Rel(len, t, NS.flush.ok(Bool.and(U32.is_le(l2, 536870912), U32.is_le((z - a : U32), 268435456)), C.BT(len, t), C.BT(l2, t2), a, z),
          Wm.flush.ok(Bool.and(U32.is_le(_, 536870912), U32.is_le((z - a : U32), 268435456)), len, t, V(l2, t2), a, z))
      flush_ok(Bool.and(U32.is_le(l2, 536870912), U32.is_le((z - a : U32), 268435456)), len, t, d, hl, l2, t2, a, z, h, hp, {==})

def flush_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, p) == True{} : Bool}) ->
  Rel(len, t, NS.flush(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}), Wm.flush(len, t, Wm{V(l2, t2), p, ok})):
  match p ok:
    case NS.Rg{+a, +z} True{}:
      flush_if(U32.is_le(z, a), len, t, d, hl, l2, t2, a, z, h, hp)
    case NS.Rg{+a, +z} False{}:
      refl(len, l2, t, t2, NS.Rg{a, z}, False{}, h, hp)

def flush_op(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  Op(len, t, w => NS.flush(w), m => Wm.flush(len, t, m)):
  +l2 => +t2 => +p => +ok => +h => +hp => flush_t(len, t, d, hl, l2, t2, p, ok, h, hp)

def push_put(+len: U32, +t: AT.Tree<U32>, +l: U32, +t0: AT.Tree<U32>, +a: U32, +z: U32, +x: U32,
  +hok: {OK(l, t0) == True{} : Bool},
  +hx: {U32.is_lt(x, 256) == True{} : Bool},
  +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hg: {Bool.and(U32.is_le(l, 536870912), U32.is_le(1, 268435456)) == True{} : Bool}) ->
  Rel(len, t, NS.push.ok(True{}, C.BT(len, t), C.BT(l, t0), z, x), Wm.push.ok(True{}, V(l, t0), z, x)):
  +hL = TW.hl29w(l, 1, N.and_true_l(U32.is_le(l, 536870912), U32.is_le(1, 268435456), hg), {==})
  +T2 = BF.RT(l, t0, 1)
  +ok2 = BF.rp_ok(l, t0, 1, T2, BF.room_p(l, t0, 1, RD.tdepth(t0), hok, hL))
  +hcap = BF.rp_cap(l, t0, 1, T2, BF.room_p(l, t0, 1, RD.tdepth(t0), hok, hL))
  +hc = {%N.le_succ_lt(U32.to_nat(l), D.cap(C.BT(l, T2))) : {_ == True{} : Bool};
    %N.add_one(U32.to_nat(l)) : {Nat.is_le(_, D.cap(C.BT(l, T2))) == True{} : Bool};
    hcap : {Nat.is_lt(U32.to_nat(l), D.cap(C.BT(l, T2))) == True{} : Bool}}
  +ept = O.push_eq_t(l, T2, x)
  +L2 = (l + 1 : U32)
  +t2 = I.set_tree(U32, T2, (l >> 2n : U32), W.put_byte(C.WD(T2, (l >> 2n : U32)), U32.to_nat((l .&. 3 : U32)), x))
  +okp = AB.subst(D.Bytes, q => {D.ok(q, RD.tdepth(T2)) == True{} : Bool}, BY.push(C.BT(l, T2), x), C.BT(L2, t2), ept, O.push_ok_t(l, T2, RD.tdepth(T2), x, ok2, hc))
  +vp = AB.subst(D.Bytes, q => {D.view(q) == List.append(&2, U32, V(l, T2), [x]) : List<&2, U32>}, BY.push(C.BT(l, T2), x), C.BT(L2, t2), ept, O.push_view_t(l, T2, RD.tdepth(T2), x, ok2, hc, hx))
  +vp2 = AB.subst(List<&2, U32>, q => {D.view(C.BT(L2, t2)) == List.append(&2, U32, q, [x]) : List<&2, U32>}, V(l, T2), V(l, t0), BF.rp_view(l, t0, 1, T2, BF.room_p(l, t0, 1, RD.tdepth(t0), hok, hL)), vp)
  %Equal.sym(D.Bytes, NR.room(C.BT(l, t0), 1), C.BT(l, T2), BF.room_eq(l, t0, 1, C.ok_full(l, t0, RD.tdepth(t0), hok))) :
    Rel(len, t, NS.Sw{C.BT(len, t), BY.push(_, x), NS.Rg{z, z}, True{}}, Wm{List.append(&2, U32, V(l, t0), [x]), NS.Rg{z, z}, True{}})
  %Equal.sym(D.Bytes, BY.push(C.BT(l, T2), x), C.BT(L2, t2), ept) :
    Rel(len, t, NS.Sw{C.BT(len, t), _, NS.Rg{z, z}, True{}}, Wm{List.append(&2, U32, V(l, t0), [x]), NS.Rg{z, z}, True{}})
  (L2, (t2, ({==}, (LM.ok_td(L2, t2, RD.tdepth(T2), okp), (vp2, pv_zz(len, a, z, hp))))))

def push_ok(+c: Bool, +len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32, +x: U32,
  +h: {OK(l2, t2) == True{} : Bool}, +hx: {U32.is_lt(x, 256) == True{} : Bool}, +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(l2, 536870912), U32.is_le(1, 268435456)) == c : Bool}) ->
  Rel(len, t, NS.push.ok(c, C.BT(len, t), C.BT(l2, t2), z, x), Wm.push.ok(c, V(l2, t2), z, x)):
  match c:
    case True{}:
      push_put(len, t, l2, t2, a, z, x, h, hx, hp, hc)
    case False{}:
      refl(len, l2, t, t2, NS.Rg{z, z}, False{}, h, pv_zz(len, a, z, hp))

def push_t(+len: U32, +t: AT.Tree<U32>, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, p) == True{} : Bool}) ->
  Rel(len, t, NS.push(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, x), Wm.push(Wm{V(l2, t2), p, ok}, x)):
  match p ok:
    case NS.Rg{+a, +z} True{}:
      %Equal.sym(U32, LN(V(l2, t2)), l2, ln_eq(l2, t2, h)) :
        Rel(len, t, NS.push.ok(Bool.and(U32.is_le(l2, 536870912), U32.is_le(1, 268435456)), C.BT(len, t), C.BT(l2, t2), z, x),
          Wm.push.ok(Bool.and(U32.is_le(_, 536870912), U32.is_le(1, 268435456)), V(l2, t2), z, x))
      push_ok(Bool.and(U32.is_le(l2, 536870912), U32.is_le(1, 268435456)), len, t, l2, t2, a, z, x, h, hx, hp, {==})
    case NS.Rg{+a, +z} False{}:
      refl(len, l2, t, t2, NS.Rg{a, z}, False{}, h, hp)

def push_op(+len: U32, +t: AT.Tree<U32>, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool}) ->
  Op(len, t, w => NS.push(w, x), m => Wm.push(m, x)):
  +l2 => +t2 => +p => +ok => +h => +hp => push_t(len, t, x, hx, l2, t2, p, ok, h, hp)

def with_p_op(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg, +hx: {PV(len, x) == True{} : Bool}) ->
  Op(len, t, w => NS.Sw.with_p(w, x), m => Wm.with_p(m, x)):
  +l2 => +t2 => +p => +ok => +h => +hp => refl(len, l2, t, t2, x, ok, h, hx)

def fail_op(+len: U32, +t: AT.Tree<U32>) ->
  Op(len, t, w => NS.Sw.fail(w), m => Wm.fail(m)):
  +l2 => +t2 => +p => +ok => +h => +hp => refl(len, l2, t, t2, p, False{}, h, hp)

# x following a .. z (x starts at z) extends it within the line.
def pv_join(+len: U32, +a: U32, +z: U32, +x: NS.Rg, +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool}, +hx: {PV(len, x) == True{} : Bool},
  +hc: {U32.is_eq(NS.Rg.a(x), z) == True{} : Bool}) -> {PV(len, NS.Rg{a, NS.Rg.z(x)}) == True{} : Bool}:
  match x:
    case NS.Rg{+xa, +xz}:
      +e = U.is_eq_true(xa, z, hc)
      +hxa = {%e : {Nat.is_le(n(_), n(xz)) == True{} : Bool}; pv_a(len, xa, xz, hx) : {Nat.is_le(n(z), n(xz)) == True{} : Bool}}
      pv_mk(len, a, xz, N.le_trans(n(a), n(z), n(xz), pv_a(len, a, z, hp), hxa), pv_z(len, xa, xz, hx))

def cpr_if(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32, +x: NS.Rg, +h: {OK(l2, t2) == True{} : Bool},
  +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool}, +hx: {PV(len, x) == True{} : Bool}, +hc: {U32.is_eq(NS.Rg.a(x), z) == c : Bool}) ->
  Rel(len, t, NS.cpr.if(c, NS.Sw{C.BT(len, t), C.BT(l2, t2), NS.Rg{a, z}, True{}}, a, x), Wm.cpr.if(c, len, t, Wm{V(l2, t2), NS.Rg{a, z}, True{}}, a, x)):
  match c:
    case True{}:
      refl(len, l2, t, t2, NS.Rg{a, NS.Rg.z(x)}, True{}, h, pv_join(len, a, z, x, hp, hx, hc))
    case False{}:
      bind(len, t, w => NS.Sw.with_p(w, x), m => Wm.with_p(m, x), with_p_op(len, t, x, hx),
        NS.flush(NS.Sw{C.BT(len, t), C.BT(l2, t2), NS.Rg{a, z}, True{}}), Wm.flush(len, t, Wm{V(l2, t2), NS.Rg{a, z}, True{}}),
        flush_t(len, t, d, hl, l2, t2, NS.Rg{a, z}, True{}, h, hp))

def cpr_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: NS.Rg, +hx: {PV(len, x) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, p) == True{} : Bool}) ->
  Rel(len, t, NS.cpr(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, x), Wm.cpr(len, t, Wm{V(l2, t2), p, ok}, x)):
  match p ok:
    case NS.Rg{+a, +z} True{}:
      cpr_if(U32.is_eq(NS.Rg.a(x), z), len, t, d, hl, l2, t2, a, z, x, h, hp, hx, {==})
    case NS.Rg{+a, +z} False{}:
      refl(len, l2, t, t2, NS.Rg{a, z}, False{}, h, hp)

def cpr_op(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: NS.Rg, +hx: {PV(len, x) == True{} : Bool}) ->
  Op(len, t, w => NS.cpr(w, x), m => Wm.cpr(len, t, m, x)):
  +l2 => +t2 => +p => +ok => +h => +hp => cpr_t(len, t, d, hl, x, hx, l2, t2, p, ok, h, hp)

# What ch does when the line's next byte is not x: copy, then push x.
def ch_push(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32, +x: U32, +h: {OK(l2, t2) == True{} : Bool},
  +hx: {U32.is_lt(x, 256) == True{} : Bool}, +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  Rel(len, t, NS.push(NS.flush(NS.Sw{C.BT(len, t), C.BT(l2, t2), NS.Rg{a, z}, True{}}), x), Wm.push(Wm.flush(len, t, Wm{V(l2, t2), NS.Rg{a, z}, True{}}), x)):
  bind(len, t, w => NS.push(w, x), m => Wm.push(m, x), push_op(len, t, x, hx),
    NS.flush(NS.Sw{C.BT(len, t), C.BT(l2, t2), NS.Rg{a, z}, True{}}), Wm.flush(len, t, Wm{V(l2, t2), NS.Rg{a, z}, True{}}),
    flush_t(len, t, d, hl, l2, t2, NS.Rg{a, z}, True{}, h, hp))

def ch_if(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32, +x: U32, +h: {OK(l2, t2) == True{} : Bool},
  +hx: {U32.is_lt(x, 256) == True{} : Bool}, +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool}, +hz: {U32.is_lt(z, len) == True{} : Bool}) ->
  Rel(len, t, NS.ch.if(c, C.BT(len, t), C.BT(l2, t2), a, z, x), Wm.ch.if(c, len, t, V(l2, t2), a, z, x)):
  match c:
    case True{}:
      refl(len, l2, t, t2, NS.Rg{a, (z + 1 : U32)}, True{}, h, pv_inc(len, t, d, a, z, hl, hp, hz))
    case False{}:
      ch_push(len, t, d, hl, l2, t2, a, z, x, h, hx, hp)

def ch_in(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +a: U32, +z: U32, +x: U32, +h: {OK(l2, t2) == True{} : Bool},
  +hx: {U32.is_lt(x, 256) == True{} : Bool}, +hp: {PV(len, NS.Rg{a, z}) == True{} : Bool}, +hz: {U32.is_lt(z, len) == c : Bool}) ->
  Rel(len, t, NS.ch.in(c, C.BT(len, t), C.BT(l2, t2), a, z, x), Wm.ch.in(c, len, t, V(l2, t2), a, z, x)):
  match c:
    case True{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), z), (C.BT(len, t), C.AT(len, t, z)), C.at_pair_t(len, t, z)) :
        Rel(len, t, NS.ch.at(_, C.BT(l2, t2), a, z, x), Wm.ch.if(U32.is_eq(C.AT(len, t, z), x), len, t, V(l2, t2), a, z, x))
      ch_if(U32.is_eq(C.AT(len, t, z), x), len, t, d, hl, l2, t2, a, z, x, h, hx, hp, hz)
    case False{}:
      ch_push(len, t, d, hl, l2, t2, a, z, x, h, hx, hp)

def ch_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, p) == True{} : Bool}) ->
  Rel(len, t, NS.ch(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, x), Wm.ch(len, t, Wm{V(l2, t2), p, ok}, x)):
  match p ok:
    case NS.Rg{+a, +z} True{}:
      ch_in(U32.is_lt(z, len), len, t, d, hl, l2, t2, a, z, x, h, hx, hp, {==})
    case NS.Rg{+a, +z} False{}:
      refl(len, l2, t, t2, NS.Rg{a, z}, False{}, h, hp)

def ch_op(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool}) ->
  Op(len, t, w => NS.ch(w, x), m => Wm.ch(len, t, m, x)):
  +l2 => +t2 => +p => +ok => +h => +hp => ch_t(len, t, d, hl, x, hx, l2, t2, p, ok, h, hp)

def sep_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +first: Bool, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {OK(l2, t2) == True{} : Bool}, +hp: {PV(len, p) == True{} : Bool}) ->
  Rel(len, t, NS.sep(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, first, x), Wm.sep(len, t, Wm{V(l2, t2), p, ok}, first, x)):
  match first:
    case True{}:
      refl(len, l2, t, t2, p, ok, h, hp)
    case False{}:
      ch_t(len, t, d, hl, x, hx, l2, t2, p, ok, h, hp)

def sep_op(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +first: Bool, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool}) ->
  Op(len, t, w => NS.sep(w, first, x), m => Wm.sep(len, t, m, first, x)):
  +l2 => +t2 => +p => +ok => +h => +hp => sep_t(len, t, d, hl, first, x, hx, l2, t2, p, ok, h, hp)
