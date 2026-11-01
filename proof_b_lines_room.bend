import Base
import ./norm_run.bend as NR
import ./proof_b_run_num.bend as NM
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# NR.room (norm_run.bend): b with room for k more bytes. For a well-formed
# mirror BT(len, t) and len + k within 2^29, the result is a well-formed
# mirror BT(len, t2) of some depth d2 with the same bytes, whose block holds
# len + k bytes. Bounds stay abstract (notes/bytes_proofs.md): 2^29 and 2^32
# are never compared with a symbolic Nat.

# Nat bounds
# ==========

def le_add2(+a: Nat, +b: Nat, +c: Nat, +e: Nat, +h1: {Nat.is_le(a, c) == True{} : Bool}, +h2: {Nat.is_le(b, e) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, b), Nat.add(c, e)) == True{} : Bool}:
  N.le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, e), N.le_add_mono_r(b, a, c, h1), N.le_add_mono_l(c, b, e, h2))

def quad(+q: Nat) ->
  {Nat.add(Nat.add(q, q), Nat.add(q, q)) == Nat.mul(4n, q) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(q, q), Nat.add(q, q)), Nat.add(q, Nat.add(q, Nat.add(q, q))), N.add_assoc(q, q, Nat.add(q, q))) :
    {_ == Nat.mul(4n, q) : Nat}
  %N.add_zero(q) : {Nat.add(q, Nat.add(q, Nat.add(q, _))) == Nat.mul(4n, q) : Nat}
  {==}

# 2^28 + 2^28 = 2^29.
def dbl28() ->
  {Nat.add(Nat.pow(2n, 28n), Nat.pow(2n, 28n)) == Nat.pow(2n, 29n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.pow(2n, 28n), Nat.pow(2n, 28n)), Nat.double(Nat.pow(2n, 28n)), Nat.pow(2n, 29n),
    Equal.sym(Nat, Nat.double(Nat.pow(2n, 28n)), Nat.add(Nat.pow(2n, 28n), Nat.pow(2n, 28n)), N.dbl_add(Nat.pow(2n, 28n))),
    Equal.sym(Nat, Nat.pow(2n, 29n), Nat.double(Nat.pow(2n, 28n)), N.pow2s(28n)))

# Two sizes within 2^28 sum within 2^29.
def le29(+a: Nat, +b: Nat, +ha: {Nat.is_le(a, Nat.pow(2n, 28n)) == True{} : Bool}, +hb: {Nat.is_le(b, Nat.pow(2n, 28n)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, b), Nat.pow(2n, 29n)) == True{} : Bool}:
  AB.subst(Nat, x => {Nat.is_le(Nat.add(a, b), x) == True{} : Bool}, Nat.add(Nat.pow(2n, 28n), Nat.pow(2n, 28n)), Nat.pow(2n, 29n), dbl28(),
    le_add2(a, b, Nat.pow(2n, 28n), Nat.pow(2n, 28n), ha, hb))

def le_mul4(+q: Nat) ->
  {Nat.is_le(q, Nat.mul(4n, q)) == True{} : Bool}:
  N.le_add_r(q, Nat.mul(3n, q))

def le28_29() ->
  {Nat.is_le(Nat.pow(2n, 28n), Nat.pow(2n, 29n)) == True{} : Bool}:
  N.pow_le(28n, 29n, {==})

# (x + 8) * 2 < 2^32 for x <= 2^29.
def ovf_y(+x: Nat, +hx: {Nat.is_le(x, Nat.pow(2n, 29n)) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(Nat.add(x, 8n), Nat.add(x, 8n)), Nat.pow(2n, 32n)) == True{} : Bool}:
  +q = Nat.pow(2n, 29n)
  +y = Nat.add(x, 8n)
  +hq8 = {N.pow_le(3n, 29n, {==}) : {Nat.is_le(8n, q) == True{} : Bool}}
  +hy = le_add2(x, 8n, q, q, hx, hq8)
  +hyy = le_add2(y, y, Nat.add(q, q), Nat.add(q, q), hy, hy)
  +h4 = AB.subst(Nat, z => {Nat.is_le(Nat.add(y, y), z) == True{} : Bool}, Nat.add(Nat.add(q, q), Nat.add(q, q)), Nat.mul(4n, q), quad(q), hyy)
  N.le_lt_trans(Nat.add(y, y), Nat.mul(4n, q), Nat.pow(2n, 32n), h4, C.four_lt_e(29n, 32n, {==}))

# The sizes room computes do not wrap.
def ovf_lk(+len: U32, +k: U32, +hx: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.pow(2n, 29n)) == True{} : Bool}) ->
  {U32.to_nat((len + k : U32)) == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}:
  +x = Nat.add(U32.to_nat(len), U32.to_nat(k))
  +y = Nat.add(x, 8n)
  U.to_nat_add_fits_p(len, k,
    N.le_lt_trans(x, Nat.add(y, y), Nat.pow(2n, 32n), N.le_trans(x, y, Nat.add(y, y), N.le_add_r(x, 8n), N.le_add_r(y, y)), ovf_y(x, hx)))

def ovf_n(+len: U32, +k: U32, +hx: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.pow(2n, 29n)) == True{} : Bool}) ->
  {U32.to_nat((len + k + 8 : U32)) == Nat.add(Nat.add(U32.to_nat(len), U32.to_nat(k)), 8n) : Nat}:
  +x = Nat.add(U32.to_nat(len), U32.to_nat(k))
  +y = Nat.add(x, 8n)
  +hlk = ovf_lk(len, k, hx)
  +h0 = N.le_lt_trans(y, Nat.add(y, y), Nat.pow(2n, 32n), N.le_add_r(y, y), ovf_y(x, hx))
  +h1 = AB.subst(Nat, w => {Nat.is_lt(Nat.add(x, w), Nat.pow(2n, 32n)) == True{} : Bool}, 8n, U32.to_nat(8), {==}, h0)
  +h = AB.subst(Nat, z => {Nat.is_lt(Nat.add(z, U32.to_nat(8)), Nat.pow(2n, 32n)) == True{} : Bool}, x, U32.to_nat((len + k : U32)), Equal.sym(Nat, U32.to_nat((len + k : U32)), x, hlk), h1)
  Equal.trans(Nat, U32.to_nat((len + k + 8 : U32)), Nat.add(U32.to_nat((len + k : U32)), 8n), y, U.to_nat_add_fits_p((len + k : U32), 8, h),
    Equal.cong(Nat, Nat, z => Nat.add(z, 8n), U32.to_nat((len + k : U32)), x, hlk))

# (len + k + 8) * 2 does not wrap.
def ovf_m2(+len: U32, +k: U32, +hx: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.pow(2n, 29n)) == True{} : Bool}) ->
  {Nat.is_lt(Nat.mul(U32.to_nat((len + k + 8 : U32)), U32.to_nat(2)), Nat.pow(2n, 32n)) == True{} : Bool}:
  +x = Nat.add(U32.to_nat(len), U32.to_nat(k))
  +y = Nat.add(x, 8n)
  +nn = (len + k + 8 : U32)
  +m2 = Equal.trans(Nat, Nat.mul(U32.to_nat(nn), U32.to_nat(2)), Nat.mul(y, U32.to_nat(2)), Nat.add(y, y),
    Equal.cong(Nat, Nat, z => Nat.mul(z, U32.to_nat(2)), U32.to_nat(nn), y, ovf_n(len, k, hx)),
    Equal.trans(Nat, Nat.mul(y, 2n), Nat.double(y), Nat.add(y, y), N.mul2_r(y), N.dbl_add(y)))
  AB.subst(Nat, z => {Nat.is_lt(z, Nat.pow(2n, 32n)) == True{} : Bool}, Nat.add(y, y), Nat.mul(U32.to_nat(nn), U32.to_nat(2)), Equal.sym(Nat, Nat.mul(U32.to_nat(nn), U32.to_nat(2)), Nat.add(y, y), m2), ovf_y(x, hx))

# depth
# =====

# 4 << j is 4 * 2^j for j <= 29.
def sh4(+j: Nat, +hj: {Nat.is_le(j, 29n) == True{} : Bool}) ->
  {U32.to_nat(U32.shln(4, j)) == Nat.mul(4n, Nat.pow(2n, j)) : Nat}:
  U.to_nat_shln_fits_p(4, j, AB.subst(Nat, w => {Nat.is_lt(Nat.mul(w, Nat.pow(2n, j)), Nat.pow(2n, 32n)) == True{} : Bool}, 4n, U32.to_nat(4), {==}, C.four_lt_e(j, 32n, C.he32(j, hj))))

def dg_step(+f: Nat, +d: Nat, +need: U32, +z: Bool, +ez: {U32.is_le(need, U32.shln(4, d)) == z : Bool}) ->
  {NR.depth.go(1n+f, d, need) == Bool.pick(Nat, z, d, NR.depth.go(f, Nat.add(d, 1n), need)) : Nat}:
  %Equal.sym(Bool, U32.is_le(need, U32.shln(4, d)), z, ez) :
    {Bool.pick(Nat, _, d, NR.depth.go(f, Nat.add(d, 1n), need)) == Bool.pick(Nat, z, d, NR.depth.go(f, Nat.add(d, 1n), need)) : Nat}
  {==}

def add1(+d: Nat, +g: Nat) ->
  {Nat.add(Nat.add(d, 1n), g) == Nat.add(d, 1n+g) : Nat}:
  N.add_assoc(d, 1n, g)

# The depth found is at most d0 + fuel.
def dg_le.k(+g: Nat, +d0: Nat, +need: U32, +z: Bool, +ez: {U32.is_le(need, U32.shln(4, d0)) == z : Bool},
  +ih: {Nat.is_le(NR.depth.go(g, Nat.add(d0, 1n), need), Nat.add(Nat.add(d0, 1n), g)) == True{} : Bool}) ->
  {Nat.is_le(NR.depth.go(1n+g, d0, need), Nat.add(d0, 1n+g)) == True{} : Bool}:
  match z:
    case True{}:
      %Equal.sym(Nat, NR.depth.go(1n+g, d0, need), d0, dg_step(g, d0, need, True{}, ez)) :
        {Nat.is_le(_, Nat.add(d0, 1n+g)) == True{} : Bool}
      N.le_add_r(d0, 1n+g)
    case False{}:
      %Equal.sym(Nat, NR.depth.go(1n+g, d0, need), NR.depth.go(g, Nat.add(d0, 1n), need), dg_step(g, d0, need, False{}, ez)) :
        {Nat.is_le(_, Nat.add(d0, 1n+g)) == True{} : Bool}
      AB.subst(Nat, x => {Nat.is_le(NR.depth.go(g, Nat.add(d0, 1n), need), x) == True{} : Bool}, Nat.add(Nat.add(d0, 1n), g), Nat.add(d0, 1n+g), add1(d0, g), ih)

def dg_le(+f: Nat, +d0: Nat, +need: U32) ->
  {Nat.is_le(NR.depth.go(f, d0, need), Nat.add(d0, f)) == True{} : Bool}:
  match f:
    case 0n:
      N.le_add_r(d0, 0n)
    case 1n+g:
      dg_le.k(g, d0, need, U32.is_le(need, U32.shln(4, d0)), {==}, dg_le(g, Nat.add(d0, 1n), need))

# The depth found is at least D when need is past 4 * 2^D.
def dg_hit.k(+dd: Nat, +d0: Nat, +need: U32, +w: Bool, +ew: {Nat.is_le(dd, d0) == w : Bool},
  +ez: {U32.is_le(need, U32.shln(4, d0)) == True{} : Bool},
  +hgt: {Nat.is_lt(Nat.mul(4n, Nat.pow(2n, dd)), U32.to_nat(need)) == True{} : Bool},
  +hd29: {Nat.is_le(dd, 29n) == True{} : Bool}) ->
  {Nat.is_le(dd, d0) == True{} : Bool}:
  match w:
    case True{}:
      ew
    case False{}:
      +hlt = N.not_le_lt(dd, d0, ew)
      +hle = N.lt_to_le(d0, dd, hlt)
      +h029 = N.le_trans(d0, dd, 29n, hle, hd29)
      +m0 = Nat.mul(4n, Nat.pow(2n, d0))
      +m1 = Nat.mul(4n, Nat.pow(2n, dd))
      +h1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(need), U32.to_nat(U32.shln(4, d0))), U32.is_le(need, U32.shln(4, d0)), True{},
        Equal.sym(Bool, U32.is_le(need, U32.shln(4, d0)), Nat.is_le(U32.to_nat(need), U32.to_nat(U32.shln(4, d0))), U.is_le_to_nat(need, U32.shln(4, d0))), ez)
      +h2 = AB.subst(Nat, x => {Nat.is_le(U32.to_nat(need), x) == True{} : Bool}, U32.to_nat(U32.shln(4, d0)), m0, sh4(d0, h029), h1)
      +h3 = N.le_mul_l(4n, Nat.pow(2n, d0), Nat.pow(2n, dd), N.pow_le(d0, dd, hle))
      +h4 = N.le_trans(U32.to_nat(need), m0, m1, h2, h3)
      +h5 = N.le_not_lt(U32.to_nat(need), m1, h4)
      Empty.absurd({Nat.is_le(dd, d0) == True{} : Bool},
        AB.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(m1, U32.to_nat(need)), False{}, Equal.sym(Bool, Nat.is_lt(m1, U32.to_nat(need)), True{}, hgt), h5)))

def dg_ge.k(+g: Nat, +d0: Nat, +need: U32, +dd: Nat, +z: Bool, +ez: {U32.is_le(need, U32.shln(4, d0)) == z : Bool},
  +hgt: {Nat.is_lt(Nat.mul(4n, Nat.pow(2n, dd)), U32.to_nat(need)) == True{} : Bool},
  +hd29: {Nat.is_le(dd, 29n) == True{} : Bool},
  +ih: {Nat.is_le(dd, NR.depth.go(g, Nat.add(d0, 1n), need)) == True{} : Bool}) ->
  {Nat.is_le(dd, NR.depth.go(1n+g, d0, need)) == True{} : Bool}:
  match z:
    case True{}:
      %Equal.sym(Nat, NR.depth.go(1n+g, d0, need), d0, dg_step(g, d0, need, True{}, ez)) :
        {Nat.is_le(dd, _) == True{} : Bool}
      dg_hit.k(dd, d0, need, Nat.is_le(dd, d0), {==}, ez, hgt, hd29)
    case False{}:
      %Equal.sym(Nat, NR.depth.go(1n+g, d0, need), NR.depth.go(g, Nat.add(d0, 1n), need), dg_step(g, d0, need, False{}, ez)) :
        {Nat.is_le(dd, _) == True{} : Bool}
      ih

def dg_ge(+f: Nat, +d0: Nat, +need: U32, +dd: Nat,
  +hd: {Nat.is_le(dd, Nat.add(d0, f)) == True{} : Bool},
  +hgt: {Nat.is_lt(Nat.mul(4n, Nat.pow(2n, dd)), U32.to_nat(need)) == True{} : Bool},
  +hd29: {Nat.is_le(dd, 29n) == True{} : Bool}) ->
  {Nat.is_le(dd, NR.depth.go(f, d0, need)) == True{} : Bool}:
  match f:
    case 0n:
      AB.subst(Nat, x => {Nat.is_le(dd, x) == True{} : Bool}, Nat.add(d0, 0n), d0, N.add_zero(d0), hd)
    case 1n+g:
      +hd2 = AB.subst(Nat, x => {Nat.is_le(dd, x) == True{} : Bool}, Nat.add(d0, 1n+g), Nat.add(Nat.add(d0, 1n), g), Equal.sym(Nat, Nat.add(Nat.add(d0, 1n), g), Nat.add(d0, 1n+g), add1(d0, g)), hd)
      dg_ge.k(g, d0, need, dd, U32.is_le(need, U32.shln(4, d0)), {==}, hgt, hd29, dg_ge(g, Nat.add(d0, 1n), need, dd, hd2, hgt, hd29))

# The block found holds x bytes when x <= need and x fits the last depth.
def dg_cap.k(+g: Nat, +d0: Nat, +need: U32, +x: Nat, +z: Bool, +ez: {U32.is_le(need, U32.shln(4, d0)) == z : Bool},
  +hx: {Nat.is_le(x, U32.to_nat(need)) == True{} : Bool},
  +h29: {Nat.is_le(Nat.add(d0, 1n+g), 29n) == True{} : Bool},
  +ih: {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, NR.depth.go(g, Nat.add(d0, 1n), need)))) == True{} : Bool}) ->
  {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, NR.depth.go(1n+g, d0, need)))) == True{} : Bool}:
  match z:
    case True{}:
      +h029 = N.le_trans(d0, Nat.add(d0, 1n+g), 29n, N.le_add_r(d0, 1n+g), h29)
      +h1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(need), U32.to_nat(U32.shln(4, d0))), U32.is_le(need, U32.shln(4, d0)), True{},
        Equal.sym(Bool, U32.is_le(need, U32.shln(4, d0)), Nat.is_le(U32.to_nat(need), U32.to_nat(U32.shln(4, d0))), U.is_le_to_nat(need, U32.shln(4, d0))), ez)
      +h2 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(need), y) == True{} : Bool}, U32.to_nat(U32.shln(4, d0)), Nat.mul(4n, Nat.pow(2n, d0)), sh4(d0, h029), h1)
      %Equal.sym(Nat, NR.depth.go(1n+g, d0, need), d0, dg_step(g, d0, need, True{}, ez)) :
        {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, _))) == True{} : Bool}
      N.le_trans(x, U32.to_nat(need), Nat.mul(4n, Nat.pow(2n, d0)), hx, h2)
    case False{}:
      %Equal.sym(Nat, NR.depth.go(1n+g, d0, need), NR.depth.go(g, Nat.add(d0, 1n), need), dg_step(g, d0, need, False{}, ez)) :
        {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, _))) == True{} : Bool}
      ih

def dg_cap(+f: Nat, +d0: Nat, +need: U32, +x: Nat,
  +hx: {Nat.is_le(x, U32.to_nat(need)) == True{} : Bool},
  +hf: {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, Nat.add(d0, f)))) == True{} : Bool},
  +h29: {Nat.is_le(Nat.add(d0, f), 29n) == True{} : Bool}) ->
  {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, NR.depth.go(f, d0, need)))) == True{} : Bool}:
  match f:
    case 0n:
      AB.subst(Nat, y => {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, y))) == True{} : Bool}, Nat.add(d0, 0n), d0, N.add_zero(d0), hf)
    case 1n+g:
      +e = Equal.sym(Nat, Nat.add(Nat.add(d0, 1n), g), Nat.add(d0, 1n+g), add1(d0, g))
      +hf2 = AB.subst(Nat, y => {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, y))) == True{} : Bool}, Nat.add(d0, 1n+g), Nat.add(Nat.add(d0, 1n), g), e, hf)
      +h292 = AB.subst(Nat, y => {Nat.is_le(y, 29n) == True{} : Bool}, Nat.add(d0, 1n+g), Nat.add(Nat.add(d0, 1n), g), e, h29)
      dg_cap.k(g, d0, need, x, U32.is_le(need, U32.shln(4, d0)), {==}, hx, h29, dg_cap(g, Nat.add(d0, 1n), need, x, hx, hf2, h292))

# room
# ====

def room_cp(+len: U32, +t: AT.Tree<U32>) -> U32:
  Pair.snd(D.Bytes, U32, BY.capacity(C.BT(len, t)))

def room_eq(+len: U32, +t: AT.Tree<U32>, +k: U32) ->
  {NR.room(C.BT(len, t), k) == NR.room.if(U32.is_le((len + k + 8 : U32), room_cp(len, t)), (len + k + 8 : U32), C.BT(len, t)) : D.Bytes}:
  %Equal.sym(D.Bytes & U32, BY.capacity(C.BT(len, t)), (C.BT(len, t), room_cp(len, t)), O.capacity_pair_t(len, t)) :
    {NR.room.k((len + k + 8 : U32), _) == NR.room.if(U32.is_le((len + k + 8 : U32), room_cp(len, t)), (len + k + 8 : U32), C.BT(len, t)) : D.Bytes}
  {==}

def RoomR(+len: U32, +t: AT.Tree<U32>, +k: U32, -r: D.Bytes) -> Data:
  Sigma<&2, &2, AT.Tree<U32>, t2 => Sigma<&2, &2, Nat, d2 =>
  Sigma<&2, &2, {r == C.BT(len, t2) : D.Bytes}, _ =>
  Sigma<&2, &2, {D.ok(C.BT(len, t2), d2) == True{} : Bool}, _ =>
  Sigma<&2, &2, {D.view(C.BT(len, t2)) == D.view(C.BT(len, t)) : List<&2, U32>}, _ =>
  {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.mul(4n, Nat.pow(2n, d2))) == True{} : Bool}>>>>>

# The capacity test, on numbers.
def room_c(+len: U32, +t: AT.Tree<U32>, +d: Nat, +k: U32, +z: Bool,
  +ez: {U32.is_le((len + k + 8 : U32), room_cp(len, t)) == z : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hx: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.pow(2n, 29n)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.add(U32.to_nat(len), U32.to_nat(k)), 8n), Nat.mul(4n, Nat.pow(2n, d))) == z : Bool}:
  +nn = (len + k + 8 : U32)
  +m = Nat.mul(4n, Nat.pow(2n, d))
  +hcp = Equal.trans(Nat, U32.to_nat(room_cp(len, t)), D.cap(C.BT(len, t)), m, O.capacity_view_t(len, t, d, hok), O.cap_ok_t(len, t, d, hok))
  +hc = Equal.trans(Bool, Nat.is_le(U32.to_nat(nn), U32.to_nat(room_cp(len, t))), U32.is_le(nn, room_cp(len, t)), z,
    Equal.sym(Bool, U32.is_le(nn, room_cp(len, t)), Nat.is_le(U32.to_nat(nn), U32.to_nat(room_cp(len, t))), U.is_le_to_nat(nn, room_cp(len, t))), ez)
  %ovf_n(len, k, hx) : {Nat.is_le(_, m) == z : Bool}
  %hcp : {Nat.is_le(U32.to_nat(nn), _) == z : Bool}
  hc

def room_ok.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +k: U32, +z: Bool,
  +ez: {U32.is_le((len + k + 8 : U32), room_cp(len, t)) == z : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hx: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.pow(2n, 29n)) == True{} : Bool}) ->
  RoomR(len, t, k, NR.room.if(z, (len + k + 8 : U32), C.BT(len, t))):
  match z:
    case True{}:
      +x = Nat.add(U32.to_nat(len), U32.to_nat(k))
      +y = Nat.add(x, 8n)
      +m = Nat.mul(4n, Nat.pow(2n, d))
      (t, (d, ({==}, (hok, ({==}, N.le_trans(x, y, m, N.le_add_r(x, 8n), room_c(len, t, d, k, True{}, ez, hok, hx)))))))
    case False{}:
      +x = Nat.add(U32.to_nat(len), U32.to_nat(k))
      +y = Nat.add(x, 8n)
      +m = Nat.mul(4n, Nat.pow(2n, d))
      +nn = (len + k + 8 : U32)
      +need = NR.want(nn)
      +e = NR.depth(need)
      +t2 = G.gtree(U32.to_nat(U32.shln(1, d)), t, G.tnew(e, 0), 0)
      +heq = G.grow_eq(len, t, d, e, C.ok_full(len, t, d, hok))
      +hd = C.ok_d(len, t, d, hok)
      +hn2 = ovf_n(len, k, hx)
      +hyw = AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(need)) == True{} : Bool}, U32.to_nat(nn), y, hn2, NM.want_ge(nn, ovf_m2(len, k, hx)))
      +hgt = N.lt_le_trans(m, y, U32.to_nat(need), N.not_le_lt(y, m, room_c(len, t, d, k, False{}, ez, hok, hx)), hyw)
      +he = dg_ge(29n, 0n, need, d, hd, hgt, hd)
      +he29 = dg_le(29n, 0n, need)
      +hok2 = AB.subst(D.Bytes, b => {D.ok(b, e) == True{} : Bool}, BY.grow(C.BT(len, t), e), C.BT(len, t2), heq, G.grow_ok_t(len, t, d, e, hok, he, he29))
      +hv2 = AB.subst(D.Bytes, b => {D.view(b) == D.view(C.BT(len, t)) : List<&2, U32>}, BY.grow(C.BT(len, t), e), C.BT(len, t2), heq, G.grow_view_t(len, t, d, e, hok, he, he29))
      +hxn = N.le_trans(x, y, U32.to_nat(need), N.le_add_r(x, 8n), hyw)
      +hxf = N.le_trans(x, Nat.pow(2n, 29n), Nat.mul(4n, Nat.pow(2n, 29n)), hx, le_mul4(Nat.pow(2n, 29n)))
      +hxf2 = AB.subst(Nat, w => {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, w))) == True{} : Bool}, 29n, Nat.add(0n, 29n), {==}, hxf)
      +hcap = AB.subst(Nat, w => {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, w))) == True{} : Bool}, NR.depth.go(29n, 0n, need), e, {==}, dg_cap(29n, 0n, need, x, hxn, hxf2, {==}))
      (t2, (e, (heq, (hok2, (hv2, hcap)))))

def room_ok(+len: U32, +t: AT.Tree<U32>, +d: Nat, +k: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hx: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.pow(2n, 29n)) == True{} : Bool}) ->
  RoomR(len, t, k, NR.room(C.BT(len, t), k)):
  %Equal.sym(D.Bytes, NR.room(C.BT(len, t), k), NR.room.if(U32.is_le((len + k + 8 : U32), room_cp(len, t)), (len + k + 8 : U32), C.BT(len, t)), room_eq(len, t, k)) :
    RoomR(len, t, k, _)
  room_ok.k(len, t, d, k, U32.is_le((len + k + 8 : U32), room_cp(len, t)), {==}, hok, hx)
