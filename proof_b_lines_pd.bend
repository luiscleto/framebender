import Base
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_fasteq.bend as FE
import ./proof_b_lines_str.bend as S
import ./proof_b_lines_lst.bend as T
import ./proof_b_lines_room.bend as R
import ./proof_b_lit.bend as LT
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-bytes@0.1.0.0/proof_find.bend as FD
import lawful-bytes@0.1.0.0/proof_same.bend as SM
import lawful-bytes@0.1.0.0/proof_seq.bend as SQ
import lawful-bytes@0.1.0.0/proof_grow.bend as G
import lawful-bytes@0.1.0.0/proof_fast_append.bend as FA
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The line end (norm.bend's Pd): what pend.add, join.k, eof_src and Pd.len
# do to it, on pictures (P.PdP). A byte line end grows through NR.put_bytes
# and NR.put_str (room, then append or push); past 2^28 bytes it becomes
# text. Near 2^28 and 2^29 every term is written exactly as the code and the
# deliverables write it (U32.to_nat, not a wrapper), so the checker never
# unfolds a power of two.

# Small facts
# ===========

def u32_le0(+x: U32) ->
  {U32.is_le(0, x) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(0, x), Nat.is_le(U32.to_nat(0), U32.to_nat(x)), True{}, U.is_le_to_nat(0, x),
    AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(x)) == True{} : Bool}, 0n, U32.to_nat(0), {==}, N.le_zero_l(U32.to_nat(x))))

# A mirror's text has its length in bytes.
def len_text(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {String.length(NR.chars(D.view(C.BT(len, t)))) == U32.to_nat(len) : Nat}:
  Equal.trans(Nat, String.length(NR.chars(D.view(C.BT(len, t)))), List.length(&2, U32, D.view(C.BT(len, t))), U32.to_nat(len),
    S.length_chars(D.view(C.BT(len, t))), O.view_size_t(len, t, d, hok))

def bytes_view(+len: U32, +t: AT.Tree<U32>) ->
  {E.is_bytes(NR.chars(D.view(C.BT(len, t)))) == True{} : Bool}:
  Equal.trans(Bool, E.is_bytes(NR.chars(D.view(C.BT(len, t)))), D.all_bytes(D.view(C.BT(len, t))), True{},
    S.bytes_chars(D.view(C.BT(len, t))), O.view_bytes_t(len, t))

def bytes_btext(+bl: U32, +bt: AT.Tree<U32>, +s: U32, +k: U32) ->
  {E.is_bytes(P.btext(bl, bt, s, k)) == True{} : Bool}:
  +V = D.view(C.BT(bl, bt))
  +sl = D.slice(V, U32.to_nat(s), U32.to_nat(k))
  Equal.trans(Bool, E.is_bytes(NR.chars(sl)), D.all_bytes(sl), True{}, S.bytes_chars(sl),
    SQ.all_bytes_take(List.drop(&2, U32, V, U32.to_nat(s)), U32.to_nat(k), T.all_bytes_drop(V, U32.to_nat(s), O.view_bytes_t(bl, bt))))

# Sizes
# =====
# The code and P.pd_ok bound a byte line end by the word 268435456 (2^28);
# LT.lit28w reads it as Nat.pow(2n, 28n). Every power of two stays a closed
# term that only meets itself, or has a variable exponent.

# a + b < 2^(3 + d) when a < 4 * 2^d and b <= 4 * 2^d (d a variable).
def sum_fit(+a: Nat, +b: Nat, +d: Nat,
  +ha: {Nat.is_lt(a, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool},
  +hb: {Nat.is_le(b, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(a, b), Nat.pow(2n, Nat.add(3n, d))) == True{} : Bool}:
  +P = Nat.pow(2n, d)
  +Q = Nat.mul(4n, P)
  +h1 = N.lt_le_trans(Nat.add(a, b), Nat.add(Q, b), Nat.add(Q, Q), N.lt_add_mono_r(b, a, Q, ha), N.le_add_mono_l(Q, b, Q, hb))
  +e1 = Equal.trans(Nat, Nat.add(Q, Q), Nat.double(Q), Nat.mul(4n, Nat.double(P)),
    Equal.sym(Nat, Nat.double(Q), Nat.add(Q, Q), N.dbl_add(Q)),
    Equal.sym(Nat, Nat.mul(4n, Nat.double(P)), Nat.double(Q), N.mul_dbl_r(4n, P)))
  +e2 = Equal.trans(Nat, Nat.mul(4n, Nat.double(P)), Nat.mul(4n, Nat.pow(2n, 1n+d)), Nat.pow(2n, Nat.add(2n, 1n+d)),
    Equal.cong(Nat, Nat, w => Nat.mul(4n, w), Nat.double(P), Nat.pow(2n, 1n+d), Equal.sym(Nat, Nat.pow(2n, 1n+d), Nat.double(P), N.pow2s(d))),
    Equal.sym(Nat, Nat.pow(2n, Nat.add(2n, 1n+d)), Nat.mul(Nat.pow(2n, 2n), Nat.pow(2n, 1n+d)), N.pow_add(2n, 2n, 1n+d)))
  AB.subst(Nat, w => {Nat.is_lt(Nat.add(a, b), w) == True{} : Bool}, Nat.add(Q, Q), Nat.pow(2n, Nat.add(3n, d)), Equal.trans(Nat, Nat.add(Q, Q), Nat.mul(4n, Nat.double(P)), Nat.pow(2n, Nat.add(3n, d)), e1, e2), h1)

def fit32(+a: Nat, +b: Nat,
  +ha: {Nat.is_lt(a, Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool},
  +hb: {Nat.is_le(b, Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(a, b), Nat.pow(2n, 32n)) == True{} : Bool}:
  AB.subst(Nat, w => {Nat.is_lt(Nat.add(a, b), Nat.pow(2n, w)) == True{} : Bool}, Nat.add(3n, 29n), 32n, {==}, sum_fit(a, b, 29n, ha, hb))

# A word at most 268435456 is at most 2^28.
def w28(+x: U32, +h: {U32.is_le(x, 268435456) == True{} : Bool}) ->
  {Nat.is_le(U32.to_nat(x), Nat.pow(2n, 28n)) == True{} : Bool}:
  AB.subst(Nat, w => {Nat.is_le(U32.to_nat(x), w) == True{} : Bool}, U32.to_nat(268435456), Nat.pow(2n, 28n), LT.lit28w(),
    Equal.trans(Bool, Nat.is_le(U32.to_nat(x), U32.to_nat(268435456)), U32.is_le(x, 268435456), True{},
      Equal.sym(Bool, U32.is_le(x, 268435456), Nat.is_le(U32.to_nat(x), U32.to_nat(268435456)), U.is_le_to_nat(x, 268435456)), h))

# And back.
def w28b(+x: U32, +h: {Nat.is_le(U32.to_nat(x), U32.to_nat(268435456)) == True{} : Bool}) ->
  {U32.is_le(x, 268435456) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(x, 268435456), Nat.is_le(U32.to_nat(x), U32.to_nat(268435456)), True{}, U.is_le_to_nat(x, 268435456), h)

# A line end within 2^28 is below 4 * 2^29.
def lt31(+x: U32, +h: {U32.is_le(x, 268435456) == True{} : Bool}) ->
  {Nat.is_lt(U32.to_nat(x), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}:
  N.le_lt_trans(U32.to_nat(x), Nat.pow(2n, 28n), Nat.mul(4n, Nat.pow(2n, 29n)), w28(x, h),
    N.lt_le_trans(Nat.pow(2n, 28n), Nat.pow(2n, 29n), Nat.mul(4n, Nat.pow(2n, 29n)), LT.pow_lt(28n, 29n, {==}), R.le_mul4(Nat.pow(2n, 29n))))

# A size within a well-formed buffer is at most 4 * 2^29.
def le31(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +x: Nat,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hx: {Nat.is_le(x, U32.to_nat(bl)) == True{} : Bool}) ->
  {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}:
  N.le_trans(x, U32.to_nat(bl), Nat.mul(4n, Nat.pow(2n, 29n)), hx,
    N.le_trans(U32.to_nat(bl), Nat.mul(4n, Nat.pow(2n, bd)), Nat.mul(4n, Nat.pow(2n, 29n)), C.ok_len(bl, bt, bd, hok),
      N.le_mul_l(4n, Nat.pow(2n, bd), Nat.pow(2n, 29n), N.pow_le(bd, 29n, C.ok_d(bl, bt, bd, hok)))))

# The ok and size parts of pd_ok.
def pd_okb(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hp: {P.pd_ok(P.PBP{len, t, d}) == True{} : Bool}) ->
  {D.ok(C.BT(len, t), d) == True{} : Bool}:
  AB.and_true_l(D.ok(C.BT(len, t), d), U32.is_le(len, 268435456), hp)

def pd_okl(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hp: {P.pd_ok(P.PBP{len, t, d}) == True{} : Bool}) ->
  {U32.is_le(len, 268435456) == True{} : Bool}:
  AB.and_true_r(D.ok(C.BT(len, t), d), U32.is_le(len, 268435456), hp)

def and_tt(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) ->
  {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pd_mk(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hl: {U32.is_le(len, 268435456) == True{} : Bool}) ->
  {P.pd_ok(P.PBP{len, t, d}) == True{} : Bool}:
  and_tt(D.ok(C.BT(len, t), d), U32.is_le(len, 268435456), hok, hl)

# Reading bytes as text
# =====================

def text_eq(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool}) ->
  {Norm.text(C.BT(bl, bt), s, k) == (C.BT(bl, bt), P.btext(bl, bt, s, k)) : D.Bytes & String}:
  +sl = Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(bl, bt), s, k))
  %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(bl, bt), s, k), (C.BT(bl, bt), sl), SM.to_list_pair_t(bl, bt, s, k)) :
    {Norm.text.k(_) == (C.BT(bl, bt), P.btext(bl, bt, s, k)) : D.Bytes & String}
  %Equal.sym(String, Norm.chars(sl), NR.chars(sl), S.chars_norm(sl)) :
    {(C.BT(bl, bt), _) == (C.BT(bl, bt), P.btext(bl, bt, s, k)) : D.Bytes & String}
  %Equal.sym(List<&2, U32>, sl, D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(k)), SM.to_list_view_t(bl, bt, bd, s, k, hok, hs)) :
    {(C.BT(bl, bt), NR.chars(_)) == (C.BT(bl, bt), P.btext(bl, bt, s, k)) : D.Bytes & String}
  {==}

def text_all(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool}) ->
  {Norm.text.all(Norm.text(C.BT(bl, bt), s, k)) == P.btext(bl, bt, s, k) : String}:
  %Equal.sym(D.Bytes & String, Norm.text(C.BT(bl, bt), s, k), (C.BT(bl, bt), P.btext(bl, bt, s, k)), text_eq(bl, bt, bd, s, k, hok, hs)) :
    {Norm.text.all(_) == P.btext(bl, bt, s, k) : String}
  {==}

def textof_eq(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {Norm.text_of(C.BT(len, t)) == NR.chars(D.view(C.BT(len, t))) : String}:
  +V = D.view(C.BT(len, t))
  %Equal.sym(String, Norm.text.all(Norm.text(C.BT(len, t), 0, len)), P.btext(len, t, 0, len), text_all(len, t, d, 0, len, hok, N.le_refl(U32.to_nat(len)))) :
    {_ == NR.chars(V) : String}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, FD.drop_zero(V)) :
    {NR.chars(List.take(&2, U32, _, U32.to_nat(len))) == NR.chars(V) : String}
  %O.view_size_t(len, t, d, hok) :
    {NR.chars(List.take(&2, U32, V, _)) == NR.chars(V) : String}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, V, List.length(&2, U32, V)), V, G.take_all(V)) :
    {NR.chars(_) == NR.chars(V) : String}
  {==}

# Bytes added to a byte line end
# ==============================

def PutR(+len: U32, +t: AT.Tree<U32>, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +k: U32, -r: D.Bytes & D.Bytes) -> Data:
  Sigma<&2, &2, U32, l3 => Sigma<&2, &2, AT.Tree<U32>, t3 => Sigma<&2, &2, Nat, d3 =>
  Sigma<&2, &2, {r == (C.BT(l3, t3), C.BT(bl, bt)) : D.Bytes & D.Bytes}, _ =>
  Sigma<&2, &2, {D.ok(C.BT(l3, t3), d3) == True{} : Bool}, _ =>
  {D.view(C.BT(l3, t3)) == List.append(&2, U32, D.view(C.BT(len, t)), D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(k))) : List<&2, U32>}>>>>>

def put_ok.m(+len: U32, +t: AT.Tree<U32>, +t2: AT.Tree<U32>, +d2: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hok2: {D.ok(C.BT(len, t2), d2) == True{} : Bool},
  +hokb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool},
  +hc: {Nat.is_le(Nat.add(D.size(C.BT(len, t2)), U32.to_nat(k)), D.cap(C.BT(len, t2))) == True{} : Bool},
  +hv2: {D.view(C.BT(len, t2)) == D.view(C.BT(len, t)) : List<&2, U32>},
  m: C.BMirror(Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k)))) ->
  PutR(len, t, bl, bt, s, k, F.append(C.BT(len, t2), C.BT(bl, bt), s, k)):
  (+l3, m2) = m
  (+t3, +e3) = m2
  +sl = D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(k))
  +heq = {
    %Equal.sym(D.Bytes & D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k), (Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k)), C.BT(bl, bt)),
      FE.append_pair(C.BT(len, t2), C.BT(bl, bt), s, k)) :
      {_ == (C.BT(l3, t3), C.BT(bl, bt)) : D.Bytes & D.Bytes}
    %e3 : {(_, C.BT(bl, bt)) == (C.BT(l3, t3), C.BT(bl, bt)) : D.Bytes & D.Bytes}
    {==} : {F.append(C.BT(len, t2), C.BT(bl, bt), s, k) == (C.BT(l3, t3), C.BT(bl, bt)) : D.Bytes & D.Bytes}}
  +hok3 = AB.subst(D.Bytes, b => {D.ok(b, d2) == True{} : Bool}, Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k)), C.BT(l3, t3),
    Equal.sym(D.Bytes, C.BT(l3, t3), Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k)), e3),
    FE.append_ok(C.BT(len, t2), C.BT(bl, bt), d2, s, k, hok2, hc))
  +hv = {
    %hv2 :
      {D.view(Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k))) == List.append(&2, U32, _, sl) : List<&2, U32>}
    FE.append_view(C.BT(len, t2), C.BT(bl, bt), d2, bd, s, k, hok2, hokb, hs, hc) :
      {D.view(Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k))) == List.append(&2, U32, D.view(C.BT(len, t)), sl) : List<&2, U32>}}
  +hv3 = AB.subst(D.Bytes, b => {D.view(b) == List.append(&2, U32, D.view(C.BT(len, t)), sl) : List<&2, U32>}, Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k)), C.BT(l3, t3),
    Equal.sym(D.Bytes, C.BT(l3, t3), Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k)), e3), hv)
  (l3, (t3, (d2, (heq, (hok3, hv3)))))

def put_ok.r(+len: U32, +t: AT.Tree<U32>, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hokb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool},
  r: R.RoomR(len, t, k, NR.room(C.BT(len, t), k))) ->
  PutR(len, t, bl, bt, s, k, NR.put_bytes(C.BT(len, t), C.BT(bl, bt), s, k)):
  (+t2, r1) = r
  (+d2, r2) = r1
  (+er, r3) = r2
  (+hok2, r4) = r3
  (+hv2, +hb2) = r4
  +hc = AB.subst(Nat, w => {Nat.is_le(Nat.add(D.size(C.BT(len, t2)), U32.to_nat(k)), w) == True{} : Bool}, Nat.mul(4n, Nat.pow(2n, d2)), D.cap(C.BT(len, t2)),
    Equal.sym(Nat, D.cap(C.BT(len, t2)), Nat.mul(4n, Nat.pow(2n, d2)), O.cap_ok_t(len, t2, d2, hok2)), hb2)
  %Equal.sym(D.Bytes, NR.room(C.BT(len, t), k), C.BT(len, t2), er) :
    PutR(len, t, bl, bt, s, k, F.append(_, C.BT(bl, bt), s, k))
  put_ok.m(len, t, t2, d2, bl, bt, bd, s, k, hok2, hokb, hs, hc, hv2, C.bmirror(Pair.fst(D.Bytes, D.Bytes, F.append(C.BT(len, t2), C.BT(bl, bt), s, k))))

def put_ok(+len: U32, +t: AT.Tree<U32>, +d: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hokb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool},
  +hx: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), Nat.pow(2n, 29n)) == True{} : Bool}) ->
  PutR(len, t, bl, bt, s, k, NR.put_bytes(C.BT(len, t), C.BT(bl, bt), s, k)):
  put_ok.r(len, t, bl, bt, bd, s, k, hokb, hs, R.room_ok(len, t, d, k, hok, hx))

# The size of the result, from its view.
def put_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +l3: U32, +t3: AT.Tree<U32>, +d3: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hokb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hok3: {D.ok(C.BT(l3, t3), d3) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool},
  +hv: {D.view(C.BT(l3, t3)) == List.append(&2, U32, D.view(C.BT(len, t)), D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(k))) : List<&2, U32>}) ->
  {U32.to_nat(l3) == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}:
  +V = D.view(C.BT(len, t))
  +sl = D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(k))
  +hsb = AB.subst(Nat, w => {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), w) == True{} : Bool}, U32.to_nat(bl), List.length(&2, U32, D.view(C.BT(bl, bt))),
    Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(bl, bt))), U32.to_nat(bl), O.view_size_t(bl, bt, bd, hokb)), hs)
  %O.view_size_t(l3, t3, d3, hok3) :
    {_ == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}
  %Equal.sym(List<&2, U32>, D.view(C.BT(l3, t3)), List.append(&2, U32, V, sl), hv) :
    {List.length(&2, U32, _) == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, V, sl)), Nat.add(List.length(&2, U32, V), List.length(&2, U32, sl)), AB.length_append(U32, V, sl)) :
    {_ == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, V), U32.to_nat(len), O.view_size_t(len, t, d, hok)) :
    {Nat.add(_, List.length(&2, U32, sl)) == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, sl), U32.to_nat(k), FA.slice_length(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(k), hsb)) :
    {Nat.add(U32.to_nat(len), _) == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}
  {==}

# An LF added to a byte line end
# ==============================

def StrR(+len: U32, +t: AT.Tree<U32>, -r: D.Bytes) -> Data:
  Sigma<&2, &2, U32, l3 => Sigma<&2, &2, AT.Tree<U32>, t3 => Sigma<&2, &2, Nat, d3 =>
  Sigma<&2, &2, {r == C.BT(l3, t3) : D.Bytes}, _ =>
  Sigma<&2, &2, {D.ok(C.BT(l3, t3), d3) == True{} : Bool}, _ =>
  {D.view(C.BT(l3, t3)) == List.append(&2, U32, D.view(C.BT(len, t)), [10]) : List<&2, U32>}>>>>>

def str_ok.m(+len: U32, +t: AT.Tree<U32>, +t2: AT.Tree<U32>, +d2: Nat,
  +hok2: {D.ok(C.BT(len, t2), d2) == True{} : Bool},
  +hc: {Nat.is_lt(D.size(C.BT(len, t2)), D.cap(C.BT(len, t2))) == True{} : Bool},
  +hv2: {D.view(C.BT(len, t2)) == D.view(C.BT(len, t)) : List<&2, U32>},
  m: C.BMirror(BY.push(C.BT(len, t2), 10))) ->
  StrR(len, t, BY.push(C.BT(len, t2), 10)):
  (+l3, m2) = m
  (+t3, +e3) = m2
  +e3s = Equal.sym(D.Bytes, C.BT(l3, t3), BY.push(C.BT(len, t2), 10), e3)
  +hok3 = AB.subst(D.Bytes, b => {D.ok(b, d2) == True{} : Bool}, BY.push(C.BT(len, t2), 10), C.BT(l3, t3), e3s, O.push_ok_t(len, t2, d2, 10, hok2, hc))
  +hv = {
    %hv2 :
      {D.view(BY.push(C.BT(len, t2), 10)) == List.append(&2, U32, _, [10]) : List<&2, U32>}
    O.push_view_t(len, t2, d2, 10, hok2, hc, {==}) :
      {D.view(BY.push(C.BT(len, t2), 10)) == List.append(&2, U32, D.view(C.BT(len, t)), [10]) : List<&2, U32>}}
  +hv3 = AB.subst(D.Bytes, b => {D.view(b) == List.append(&2, U32, D.view(C.BT(len, t)), [10]) : List<&2, U32>}, BY.push(C.BT(len, t2), 10), C.BT(l3, t3), e3s, hv)
  (l3, (t3, (d2, (e3s, (hok3, hv3)))))

def str_ok.r(+len: U32, +t: AT.Tree<U32>,
  r: R.RoomR(len, t, U32.from_nat(String.length("\n")), NR.room(C.BT(len, t), U32.from_nat(String.length("\n"))))) ->
  StrR(len, t, NR.put_str(C.BT(len, t), "\n")):
  (+t2, r1) = r
  (+d2, r2) = r1
  (+er, r3) = r2
  (+hok2, r4) = r3
  (+hv2, +hb2) = r4
  +L = U32.to_nat(len)
  +M = Nat.mul(4n, Nat.pow(2n, d2))
  +hb3 = AB.subst(Nat, w => {Nat.is_le(Nat.add(L, w), M) == True{} : Bool}, U32.to_nat(U32.from_nat(String.length("\n"))), 1n, {==}, hb2)
  +hb4 = AB.subst(Nat, w => {Nat.is_le(w, M) == True{} : Bool}, Nat.add(L, 1n), 1n+L, N.add_one(L), hb3)
  +hlt = Equal.trans(Bool, Nat.is_lt(L, M), Nat.is_le(1n+L, M), True{}, Equal.sym(Bool, Nat.is_le(1n+L, M), Nat.is_lt(L, M), N.le_succ_lt(L, M)), hb4)
  +hc = AB.subst(Nat, w => {Nat.is_lt(D.size(C.BT(len, t2)), w) == True{} : Bool}, M, D.cap(C.BT(len, t2)),
    Equal.sym(Nat, D.cap(C.BT(len, t2)), M, O.cap_ok_t(len, t2, d2, hok2)), hlt)
  %Equal.sym(D.Bytes, NR.room(C.BT(len, t), U32.from_nat(String.length("\n"))), C.BT(len, t2), er) :
    StrR(len, t, NR.put_str.go("\n", _))
  str_ok.m(len, t, t2, d2, hok2, hc, hv2, C.bmirror(BY.push(C.BT(len, t2), 10)))

def str_ok(+len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hl: {U32.is_le(len, 268435456) == True{} : Bool}) ->
  StrR(len, t, NR.put_str(C.BT(len, t), "\n")):
  +k = U32.from_nat(String.length("\n"))
  +P28 = Nat.pow(2n, 28n)
  +h1 = AB.subst(Nat, w => {Nat.is_le(w, P28) == True{} : Bool}, 1n, U32.to_nat(k), {==},
    Equal.trans(Bool, Nat.is_le(1n, P28), Nat.is_lt(0n, P28), True{}, N.le_succ_lt(0n, P28), N.pow_pos(28n)))
  str_ok.r(len, t, R.room_ok(len, t, d, k, hok, R.le29(U32.to_nat(len), U32.to_nat(k), w28(len, hl), h1)))

# The deliverables (proof_b_lines.bend), every argument reusable
# ==============================================================

def and_le0(+a: Bool, +l: U32, +ha: {a == True{} : Bool}) ->
  {Bool.and(a, U32.is_le(0, l)) == True{} : Bool}:
  and_tt(a, U32.is_le(0, l), ha, u32_le0(l))

def pd_len.go(+pp: P.PdP, +hp: {P.pd_ok(pp) == True{} : Bool}) ->
  {Norm.Pd.len(P.mkPd(pp)) == (P.mkPd(pp), String.length(P.pdtext(pp))) : Norm.Pd & Nat}:
  match pp:
    case P.PBP{+len, +t, +d}:
      %Equal.sym(Nat, String.length(NR.chars(D.view(C.BT(len, t)))), U32.to_nat(len), len_text(len, t, d, pd_okb(len, t, d, hp))) :
        {Norm.Pd.len(P.mkPd(P.PBP{len, t, d})) == (P.mkPd(P.PBP{len, t, d}), _) : Norm.Pd & Nat}
      {==}
    case P.PSP{+str}:
      {==}

def pd_empty.go() ->
  &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd}
  & ({P.pd_ok(pp) == True{} : Bool}
  & {P.pdtext(pp) == "" : String})):
  (P.PBP{0, G.tnew(0n, 0), 0n}, (Equal.cong(D.Bytes, Norm.Pd, b => Norm.PB{b}, BY.empty(0n), C.BT(0, G.tnew(0n, 0)), G.empty_eq(0n)), ({==}, {==})))

def eof_txt(+len: U32, +t: AT.Tree<U32>, +l3: U32, +t3: AT.Tree<U32>,
  +hv: {D.view(C.BT(l3, t3)) == List.append(&2, U32, D.view(C.BT(len, t)), [10]) : List<&2, U32>}) ->
  {NR.chars(List.drop(&2, U32, D.view(C.BT(l3, t3)), U32.to_nat(0))) == String.append(NR.chars(D.view(C.BT(len, t))), "\n") : String}:
  +V = D.view(C.BT(len, t))
  +W = D.view(C.BT(l3, t3))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, W, 0n), W, FD.drop_zero(W)) : {NR.chars(_) == String.append(NR.chars(V), "\n") : String}
  %Equal.sym(List<&2, U32>, W, List.append(&2, U32, V, [10]), hv) : {NR.chars(_) == String.append(NR.chars(V), "\n") : String}
  S.chars_app(V, [10])

def eof_ok.b(+len: U32, +t: AT.Tree<U32>, r: StrR(len, t, NR.put_str(C.BT(len, t), "\n"))) ->
  &sp: P.SrcP -> ({Norm.eof_src(Norm.PB{C.BT(len, t)}) == P.mkSrc(sp) : Norm.Src}
  & ({P.src_ok(sp) == True{} : Bool}
  & {P.srctext(sp) == String.append(NR.chars(D.view(C.BT(len, t))), "\n") : String})):
  (+l3, r1) = r
  (+t3, r2) = r1
  (+d3, r3) = r2
  (+e, r4) = r3
  (+ok3, +v3) = r4
  (P.SBP{l3, t3, d3, 0}, (Equal.cong(D.Bytes, Norm.Src, b => Norm.SB{b, 0}, NR.put_str(C.BT(len, t), "\n"), C.BT(l3, t3), e),
    (and_le0(D.ok(C.BT(l3, t3), d3), l3, ok3), eof_txt(len, t, l3, t3, v3))))

def eof_ok.go(+pp: P.PdP, +hp: {P.pd_ok(pp) == True{} : Bool}, +hn: {P.nolf(P.pdtext(pp)) == True{} : Bool}) ->
  &sp: P.SrcP -> ({Norm.eof_src(P.mkPd(pp)) == P.mkSrc(sp) : Norm.Src}
  & ({P.src_ok(sp) == True{} : Bool}
  & {P.srctext(sp) == String.append(P.pdtext(pp), "\n") : String})):
  match pp:
    case P.PBP{+len, +t, +d}:
      eof_ok.b(len, t, str_ok(len, t, d, pd_okb(len, t, d, hp), pd_okl(len, t, d, hp)))
    case P.PSP{+str}:
      (P.SLP{str}, ({==}, (and_tt(E.is_bytes(str), P.nolf(str), hp, hn), {==})))

def PendR(+pp: P.PdP, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +k: U32, -r: Norm.Pd) -> Type:
  &pp2: P.PdP -> ({r == P.mkPd(pp2) : Norm.Pd}
  & ({P.pd_ok(pp2) == True{} : Bool}
  & {P.pdtext(pp2) == String.append(P.pdtext(pp), P.btext(bl, bt, s, k)) : String}))

# The sum the code tests does not wrap.
def sum_w(+len: U32, +k: U32, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat,
  +hl: {U32.is_le(len, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_le(U32.to_nat(k), U32.to_nat(bl)) == True{} : Bool}) ->
  {U32.to_nat((len + k : U32)) == Nat.add(U32.to_nat(len), U32.to_nat(k)) : Nat}:
  U.to_nat_add_fits_p(len, k, fit32(U32.to_nat(len), U32.to_nat(k), lt31(len, hl), le31(bl, bt, bd, U32.to_nat(k), hok, hk)))

# A small byte line end: the bytes appended.
def pend_add.b(+len: U32, +t: AT.Tree<U32>, +d: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hokp: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(len), U32.to_nat(k)), U32.to_nat(268435456)) == True{} : Bool},
  r: PutR(len, t, bl, bt, s, k, NR.put_bytes(C.BT(len, t), C.BT(bl, bt), s, k))) ->
  PendR(P.PBP{len, t, d}, bl, bt, s, k, Norm.pend.add.b(NR.put_bytes(C.BT(len, t), C.BT(bl, bt), s, k))):
  (+l3, r1) = r
  (+t3, r2) = r1
  (+d3, r3) = r2
  (+e, r4) = r3
  (+ok3, +v3) = r4
  +V = D.view(C.BT(len, t))
  +sl = D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(k))
  +hl3 = put_len(len, t, d, l3, t3, d3, bl, bt, bd, s, k, hokp, hok, ok3, hs, v3)
  +hl28 = w28b(l3, AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(268435456)) == True{} : Bool}, Nat.add(U32.to_nat(len), U32.to_nat(k)), U32.to_nat(l3),
    Equal.sym(Nat, U32.to_nat(l3), Nat.add(U32.to_nat(len), U32.to_nat(k)), hl3), hsz))
  +heq = {
    %Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(len, t), C.BT(bl, bt), s, k), (C.BT(l3, t3), C.BT(bl, bt)), e) :
      {Norm.pend.add.b(_) == Norm.PB{C.BT(l3, t3)} : Norm.Pd}
    {==} : {Norm.pend.add.b(NR.put_bytes(C.BT(len, t), C.BT(bl, bt), s, k)) == P.mkPd(P.PBP{l3, t3, d3}) : Norm.Pd}}
  +htx = {
    %Equal.sym(List<&2, U32>, D.view(C.BT(l3, t3)), List.append(&2, U32, V, sl), v3) :
      {NR.chars(_) == String.append(NR.chars(V), NR.chars(sl)) : String}
    S.chars_app(V, sl) : {P.pdtext(P.PBP{l3, t3, d3}) == String.append(P.pdtext(P.PBP{len, t, d}), P.btext(bl, bt, s, k)) : String}}
  (P.PBP{l3, t3, d3}, (heq, (pd_mk(l3, t3, d3, ok3, hl28), htx)))

def pend_add.bk(+len: U32, +t: AT.Tree<U32>, +d: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32, +z: Bool,
  +ez: {U32.is_le((len + k : U32), 268435456) == z : Bool},
  +hp: {P.pd_ok(P.PBP{len, t, d}) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool}) ->
  PendR(P.PBP{len, t, d}, bl, bt, s, k, Norm.pend.add.bk(z, C.BT(len, t), C.BT(bl, bt), s, k)):
  match z:
    case True{}:
      +hokp = pd_okb(len, t, d, hp)
      +X = Nat.add(U32.to_nat(len), U32.to_nat(k))
      +hw = sum_w(len, k, bl, bt, bd, pd_okl(len, t, d, hp), hok, N.le_trans(U32.to_nat(k), Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl), N.le_add_l(U32.to_nat(k), U32.to_nat(s)), hs))
      +hsz = AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(268435456)) == True{} : Bool}, U32.to_nat((len + k : U32)), X, hw,
        Equal.trans(Bool, Nat.is_le(U32.to_nat((len + k : U32)), U32.to_nat(268435456)), U32.is_le((len + k : U32), 268435456), True{},
          Equal.sym(Bool, U32.is_le((len + k : U32), 268435456), Nat.is_le(U32.to_nat((len + k : U32)), U32.to_nat(268435456)), U.is_le_to_nat((len + k : U32), 268435456)), ez))
      +h28 = AB.subst(Nat, w => {Nat.is_le(X, w) == True{} : Bool}, U32.to_nat(268435456), Nat.pow(2n, 28n), LT.lit28w(), hsz)
      +hx = N.le_trans(X, Nat.pow(2n, 28n), Nat.pow(2n, 29n), h28, R.le28_29())
      pend_add.b(len, t, d, bl, bt, bd, s, k, hokp, hok, hs, hsz, put_ok(len, t, d, bl, bt, bd, s, k, hokp, hok, hs, hx))
    case False{}:
      +hokp = pd_okb(len, t, d, hp)
      +heq = {
        %Equal.sym(String, Norm.text_of(C.BT(len, t)), NR.chars(D.view(C.BT(len, t))), textof_eq(len, t, d, hokp)) :
          {Norm.PS{String.append(_, Norm.text.all(Norm.text(C.BT(bl, bt), s, k)))} == Norm.PS{String.append(NR.chars(D.view(C.BT(len, t))), P.btext(bl, bt, s, k))} : Norm.Pd}
        %Equal.sym(String, Norm.text.all(Norm.text(C.BT(bl, bt), s, k)), P.btext(bl, bt, s, k), text_all(bl, bt, bd, s, k, hok, hs)) :
          {Norm.PS{String.append(NR.chars(D.view(C.BT(len, t))), _)} == Norm.PS{String.append(NR.chars(D.view(C.BT(len, t))), P.btext(bl, bt, s, k))} : Norm.Pd}
        {==} : {Norm.pend.add.bk(False{}, C.BT(len, t), C.BT(bl, bt), s, k) == P.mkPd(P.PSP{String.append(NR.chars(D.view(C.BT(len, t))), P.btext(bl, bt, s, k))}) : Norm.Pd}}
      (P.PSP{String.append(NR.chars(D.view(C.BT(len, t))), P.btext(bl, bt, s, k))},
        (heq, (S.bytes_app(NR.chars(D.view(C.BT(len, t))), P.btext(bl, bt, s, k), bytes_view(len, t), bytes_btext(bl, bt, s, k)), {==})))

def pend_add.go(+pp: P.PdP, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  +hp: {P.pd_ok(pp) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(bl)) == True{} : Bool}) ->
  PendR(pp, bl, bt, s, k, Norm.pend.add(P.mkPd(pp), C.BT(bl, bt), s, k)):
  match pp:
    case P.PBP{+len, +t, +d}:
      pend_add.bk(len, t, d, bl, bt, bd, s, k, U32.is_le((len + k : U32), 268435456), {==}, hp, hok, hs)
    case P.PSP{+str}:
      +heq = {
        %Equal.sym(String, Norm.text.all(Norm.text(C.BT(bl, bt), s, k)), P.btext(bl, bt, s, k), text_all(bl, bt, bd, s, k, hok, hs)) :
          {Norm.PS{String.append(str, _)} == Norm.PS{String.append(str, P.btext(bl, bt, s, k))} : Norm.Pd}
        {==} : {Norm.pend.add(P.mkPd(P.PSP{str}), C.BT(bl, bt), s, k) == P.mkPd(P.PSP{String.append(str, P.btext(bl, bt, s, k))}) : Norm.Pd}}
      (P.PSP{String.append(str, P.btext(bl, bt, s, k))}, (heq, (S.bytes_app(str, P.btext(bl, bt, s, k), hp, bytes_btext(bl, bt, s, k)), {==})))

# k + 1 does not wrap for k below a buffer's length.
def k1(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +k: U32,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_lt(U32.to_nat(k), U32.to_nat(bl)) == True{} : Bool}) ->
  {U32.to_nat((k + 1 : U32)) == Nat.add(U32.to_nat(k), 1n) : Nat}:
  C.inc_fits(k, bd, C.ok_d(bl, bt, bd, hok), N.lt_le_trans(U32.to_nat(k), U32.to_nat(bl), Nat.mul(4n, Nat.pow(2n, bd)), hk, C.ok_len(bl, bt, bd, hok)))

# The line through its LF (byte k) is the line before it, then "\n".
def bt_lf(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +k: U32,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_lt(U32.to_nat(k), U32.to_nat(bl)) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(C.BT(bl, bt)), U32.to_nat(k)) == Some{10} : Maybe<&2, U32>}) ->
  {P.btext(bl, bt, 0, (k + 1 : U32)) == String.append(P.btext(bl, bt, 0, k), "\n") : String}:
  +V = D.view(C.BT(bl, bt))
  +K = U32.to_nat(k)
  +hk1 = k1(bl, bt, bd, k, hok, hk)
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, FD.drop_zero(V)) :
    {NR.chars(List.take(&2, U32, _, U32.to_nat((k + 1 : U32)))) == String.append(NR.chars(List.take(&2, U32, _, K)), "\n") : String}
  %Equal.sym(Nat, U32.to_nat((k + 1 : U32)), Nat.add(K, 1n), hk1) :
    {NR.chars(List.take(&2, U32, V, _)) == String.append(NR.chars(List.take(&2, U32, V, K)), "\n") : String}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, V, Nat.add(K, 1n)), List.append(&2, U32, List.take(&2, U32, V, K), [10]), G.take_succ_get(V, K, 10, hlf)) :
    {NR.chars(_) == String.append(NR.chars(List.take(&2, U32, V, K)), "\n") : String}
  S.chars_app(List.take(&2, U32, V, K), [10])


# join.l's sum (len + k) + 1 does not wrap: it is len + (k + 1).
def wk1(+len: U32, +k: U32, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat,
  +hl: {U32.is_le(len, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_lt(U32.to_nat(k), U32.to_nat(bl)) == True{} : Bool}) ->
  {U32.to_nat(((len + k : U32) + 1 : U32)) == Nat.add(U32.to_nat(len), U32.to_nat((k + 1 : U32))) : Nat}:
  +a = U32.to_nat(len)
  +b = U32.to_nat(k)
  +hk1 = k1(bl, bt, bd, k, hok, hk)
  +hlk = sum_w(len, k, bl, bt, bd, hl, hok, N.lt_to_le(b, U32.to_nat(bl), hk))
  +hb1 = AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(bl)) == True{} : Bool}, Nat.add(b, 1n), U32.to_nat((k + 1 : U32)),
    Equal.sym(Nat, U32.to_nat((k + 1 : U32)), Nat.add(b, 1n), hk1), C.succ_le(b, U32.to_nat(bl), hk))
  +hf = fit32(a, U32.to_nat((k + 1 : U32)), lt31(len, hl), le31(bl, bt, bd, U32.to_nat((k + 1 : U32)), hok, hb1))
  +e = Equal.trans(Nat, Nat.add(U32.to_nat((len + k : U32)), U32.to_nat(1)), Nat.add(Nat.add(a, b), 1n), Nat.add(a, U32.to_nat((k + 1 : U32))),
    Equal.cong(Nat, Nat, w => Nat.add(w, 1n), U32.to_nat((len + k : U32)), Nat.add(a, b), hlk),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), 1n), Nat.add(a, Nat.add(b, 1n)), Nat.add(a, U32.to_nat((k + 1 : U32))), N.add_assoc(a, b, 1n),
      Equal.cong(Nat, Nat, w => Nat.add(a, w), Nat.add(b, 1n), U32.to_nat((k + 1 : U32)), Equal.sym(Nat, U32.to_nat((k + 1 : U32)), Nat.add(b, 1n), hk1))))
  +h = AB.subst(Nat, w => {Nat.is_lt(w, Nat.pow(2n, 32n)) == True{} : Bool}, Nat.add(a, U32.to_nat((k + 1 : U32))), Nat.add(U32.to_nat((len + k : U32)), U32.to_nat(1)),
    Equal.sym(Nat, Nat.add(U32.to_nat((len + k : U32)), U32.to_nat(1)), Nat.add(a, U32.to_nat((k + 1 : U32))), e), hf)
  Equal.trans(Nat, U32.to_nat(((len + k : U32) + 1 : U32)), Nat.add(U32.to_nat((len + k : U32)), U32.to_nat(1)), Nat.add(a, U32.to_nat((k + 1 : U32))),
    U.to_nat_add_fits_p((len + k : U32), 1, h), e)
