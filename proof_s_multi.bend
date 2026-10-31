import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_cut.bend as K
import ./proof_s_scan.bend as SC
import ./proof_s_line.bend as LI
import ./proof_s_drv.bend as DR
import ./proof_base.bend as P
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import ./proof_b_fasteq.bend as FE
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-fields@0.1.0.0/fields.bend as FC
import lawful-fields@0.1.0.0/LAWS.bend as FL
import lawful-fields@0.1.0.0/PROOF.bend as FP
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The test before the fast path (norm_split.bend's multi): when it answers
# None for a complete line, the line has at most one ALT, so B.Rec.parts
# leaves it whole. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def V(+len: U32, +t: AT.Tree<U32>) -> L32():
  D.view(C.BT(len, t))

# ---------------------------------------------------------------------------
# The code: multi on a line whose LF is at lf
# ---------------------------------------------------------------------------

# The first LF from s is at lf.
def find_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +lf: U32,
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hfst: {n(lf) == D.first(V(len, t), n(s), n(len), 10) : Nat}) ->
  {F.find(C.BT(len, t), s, len, 10) == (C.BT(len, t), lf) : D.Bytes & U32}:
  +j = Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), s, len, 10))
  +ej = U.to_nat_inj(j, lf, Equal.trans(Nat, n(j), D.first(V(len, t), n(s), n(len), 10), n(lf),
    PF.find_view_t(len, t, d, s, len, 10, hl, hs, N.le_refl(n(len)), {==}), Equal.sym(Nat, n(lf), D.first(V(len, t), n(s), n(len), 10), hfst)))
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s, len, 10), BY.find(C.BT(len, t), s, len, 10), FE.find_eq(C.BT(len, t), d, s, len, 10, hl, hs, N.le_refl(n(len)), {==})) : {_ == (C.BT(len, t), lf) : D.Bytes & U32}
  %Equal.sym(D.Bytes & U32, BY.find(C.BT(len, t), s, len, 10), (C.BT(len, t), j), PF.find_pair_t(len, t, s, len, 10)) : {_ == (C.BT(len, t), lf) : D.Bytes & U32}
  %Equal.sym(U32, j, lf, ej) : {(C.BT(len, t), _) == (C.BT(len, t), lf) : D.Bytes & U32}
  {==}

# The first five ends of the body (cut at tabs).
def ES5(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32) -> L32():
  Pair.snd(D.Bytes, L32(), FC.cut(C.BT(len, t), s, be, 9, 5n))

law multi_es:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +s: U32
  for +lf: U32
  for +hsl: {Nat.is_le(n(s), n(lf)) == True{} : Bool}
  for +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  for +hfst: {n(lf) == D.first(V(len, t), n(s), n(len), 10) : Nat}
  {NS.multi(C.BT(len, t), s) == NS.multi.es(ES5(len, t, s, LI.BE(len, t, s, lf)), C.BT(len, t), lf) : D.Bytes & Maybe<&2, U32>}

def multi_es(len, t, d, hl, s, lf, hsl, hlf, hfst):
  +be = LI.BE(len, t, s, lf)
  +hsle = DR.be_lo.k(len, t, s, lf, hsl, U32.is_lt(s, lf), {==})
  +hbel = N.le_trans(n(be), n(lf), n(len), DR.be_hi.k(len, t, s, lf, U32.is_lt(s, lf), {==}), N.lt_to_le(n(lf), n(len), hlf))
  +hs = Equal.trans(Bool, U32.is_le(s, len), Nat.is_le(n(s), n(len)), True{}, U.is_le_to_nat(s, len), N.le_trans(n(s), n(lf), n(len), hsl, N.lt_to_le(n(lf), n(len), hlf)))
  +hsb = Equal.trans(Bool, U32.is_le(s, be), Nat.is_le(n(s), n(be)), True{}, U.is_le_to_nat(s, be), hsle)
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s, len, 10), (C.BT(len, t), lf), find_lf(len, t, d, hl, s, lf, hs, hfst)) :
    {NS.multi.lf(s, _, len) == NS.multi.es(ES5(len, t, s, be), C.BT(len, t), lf) : D.Bytes & Maybe<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(lf, len), True{}, LI.ult(lf, len, hlf)) :
    {NS.multi.lf.if(_, C.BT(len, t), s, lf) == NS.multi.es(ES5(len, t, s, be), C.BT(len, t), lf) : D.Bytes & Maybe<&2, U32>}
  %DR.at_s(len, t, Bool.pick(U32, U32.is_lt(s, lf), (lf - 1 : U32), lf)) :
    {NS.multi.cr(_, s, lf) == NS.multi.es(ES5(len, t, s, be), C.BT(len, t), lf) : D.Bytes & Maybe<&2, U32>}
  %Equal.sym(D.Bytes & L32(), NS.cut.ends(C.BT(len, t), s, be, 9, 5n), FC.cut(C.BT(len, t), s, be, 9, 5n), K.ends_eq(len, t, d, s, be, 9, 5n, hl, hsb, hbel, {==})) :
    {NS.multi.cut(_, lf) == NS.multi.es(ES5(len, t, s, be), C.BT(len, t), lf) : D.Bytes & Maybe<&2, U32>}
  %Equal.sym(D.Bytes & L32(), FC.cut(C.BT(len, t), s, be, 9, 5n), (C.BT(len, t), ES5(len, t, s, be)), FL.cut_pair(C.BT(len, t), s, be, 9, 5n)) :
    {NS.multi.cut(_, lf) == NS.multi.es(ES5(len, t, s, be), C.BT(len, t), lf) : D.Bytes & Maybe<&2, U32>}
  {==}

# ---------------------------------------------------------------------------
# The spec: the fields are the pieces of the body's bytes at tabs
# ---------------------------------------------------------------------------

def LL() -> Data:
  List<&2, List<&2, U32>>

def Ss() -> Data:
  List<&2, String>

def Ns() -> Data:
  List<&2, Nat>

# The body's bytes s .. be-1, and their pieces at tabs.
def BV(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32) -> L32():
  D.slice(V(len, t), n(s), Nat.sub(n(be), n(s)))

def SPV(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32) -> LL():
  FD.split(BV(len, t, s, be), 9)

def flds(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32, +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool}) ->
  {B.Rec.fields(LI.TXR(len, t, s, be)) == FD.texts(SPV(len, t, s, be)) : Ss()}:
  +xs = BV(len, t, s, be)
  %Equal.sym(Nat, n((be - s : U32)), Nat.sub(n(be), n(s)), W.nsub(s, be, hn)) :
    {String.split(NR.chars(D.slice(V(len, t), n(s), _)), Chr{9}) == FD.texts(FD.split(xs, 9)) : Ss()}
  %K.text_chars(xs) : {String.split(_, Chr{9}) == FD.texts(FD.split(xs, 9)) : Ss()}
  FL.split_text(xs, 9)

def texts_len(ps: LL()) -> {List.length(&2, String, FD.texts(ps)) == List.length(&2, L32(), ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, String, FD.texts(r)), List.length(&2, L32(), r), texts_len(r))

# At least five pieces.
def has1(l: LL()) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{h, r}:
      True{}

def has2(l: LL()) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{h, r}:
      has1(r)

def has3(l: LL()) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{h, r}:
      has2(r)

def has4(l: LL()) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{h, r}:
      has3(r)

def has5(l: LL()) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{h, r}:
      has4(r)

def g3(l: Ns()) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, l, 3n), 0n)

def g4(l: Ns()) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, l, 4n), 0n)

def get4(l: LL()) -> Maybe<&2, L32()>:
  List.get(&2, L32(), l, 4n)

def unsome(m: Maybe<&2, L32()>) -> L32():
  Maybe.default(&2, L32(), m, Nil{})

def E5(+e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +r: L32()) -> L32():
  Con{e0, Con{e1, Con{e2, Con{e3, Con{e4, r}}}}}

def P5(+q0: L32(), +q1: L32(), +q2: L32(), +q3: L32(), +q4: L32(), +r: LL()) -> LL():
  Con{q0, Con{q1, Con{q2, Con{q3, Con{q4, r}}}}}

# The fifth piece (the ALT field), between the fourth and fifth ends.
def P4(+len: U32, +t: AT.Tree<U32>, +e3: U32, +e4: U32) -> L32():
  D.slice(V(len, t), Nat.add(n(e3), 1n), Nat.sub(n(e4), Nat.add(n(e3), 1n)))

def FIVE(+len: U32, +t: AT.Tree<U32>, +ps: LL(), +e3: U32, +e4: U32) -> Type:
  {List.get(&2, String, FD.texts(ps), 4n) == Some{FD.text(P4(len, t, e3, e4))} : Maybe<&2, String>} &
  {n(e4) == Nat.add(Nat.add(n(e3), 1n), List.length(&2, U32, P4(len, t, e3, e4))) : Nat}

def five.p(+len: U32, +t: AT.Tree<U32>, +f: Nat, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +r: L32(),
  +q0: L32(), +q1: L32(), +q2: L32(), +q3: L32(), +q4: L32(), +rest: LL(),
  +hE: {FD.nats(E5(e0, e1, e2, e3, e4, r)) == List.take(&2, Nat, FD.ends(P5(q0, q1, q2, q3, q4, rest), f), 5n) : Ns()},
  +hP: {FD.pieces(E5(e0, e1, e2, e3, e4, r), V(len, t), f) == List.take(&2, L32(), P5(q0, q1, q2, q3, q4, rest), 5n) : LL()}) ->
  FIVE(len, t, P5(q0, q1, q2, q3, q4, rest), e3, e4):
  +A = P4(len, t, e3, e4)
  +TE = List.take(&2, Nat, FD.ends(P5(q0, q1, q2, q3, q4, rest), f), 5n)
  +X3 = g3(TE)
  +eA = Equal.cong(Maybe<&2, L32()>, L32(), unsome, Some{A}, Some{q4},
    Equal.cong(LL(), Maybe<&2, L32()>, get4, FD.pieces(E5(e0, e1, e2, e3, e4, r), V(len, t), f), List.take(&2, L32(), P5(q0, q1, q2, q3, q4, rest), 5n), hP))
  +h3 = Equal.cong(Ns(), Nat, g3, FD.nats(E5(e0, e1, e2, e3, e4, r)), TE, hE)
  +h4 = Equal.cong(Ns(), Nat, g4, FD.nats(E5(e0, e1, e2, e3, e4, r)), TE, hE)
  (Equal.cong(L32(), Maybe<&2, String>, x => Some{FD.text(x)}, q4, A, Equal.sym(L32(), A, q4, eA)),
    Equal.trans(Nat, n(e4), g4(TE), Nat.add(Nat.add(n(e3), 1n), List.length(&2, U32, A)), h4,
      {%Equal.sym(Nat, n(e3), X3, h3) : {g4(TE) == Nat.add(Nat.add(_, 1n), List.length(&2, U32, A)) : Nat};
       %Equal.sym(L32(), A, q4, eA) : {g4(TE) == Nat.add(Nat.add(X3, 1n), List.length(&2, U32, _)) : Nat};
       {==} : {g4(TE) == Nat.add(Nat.add(n(e3), 1n), List.length(&2, U32, A)) : Nat}}))

def five.no(+len: U32, +t: AT.Tree<U32>, +f: Nat, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +r: L32(), +ps: LL(),
  +hP: {FD.pieces(E5(e0, e1, e2, e3, e4, r), V(len, t), f) == List.take(&2, L32(), ps, 5n) : LL()},
  +h5: {has5(List.take(&2, L32(), ps, 5n)) == False{} : Bool}) -> FIVE(len, t, ps, e3, e4):
  Empty.absurd(FIVE(len, t, ps, e3, e4), P.false_ne_true(Equal.trans(Bool, False{}, has5(List.take(&2, L32(), ps, 5n)), True{},
    Equal.sym(Bool, has5(List.take(&2, L32(), ps, 5n)), False{}, h5),
    Equal.sym(Bool, True{}, has5(List.take(&2, L32(), ps, 5n)), Equal.cong(LL(), Bool, has5, FD.pieces(E5(e0, e1, e2, e3, e4, r), V(len, t), f), List.take(&2, L32(), ps, 5n), hP)))))

# Five ends: the fifth piece is the ALT field, and the fifth end follows the
# fourth.
law five:
  for +len: U32
  for +t: AT.Tree<U32>
  for +f: Nat
  for +e0: U32
  for +e1: U32
  for +e2: U32
  for +e3: U32
  for +e4: U32
  for +r: L32()
  for +ps: LL()
  for +hE: {FD.nats(E5(e0, e1, e2, e3, e4, r)) == List.take(&2, Nat, FD.ends(ps, f), 5n) : Ns()}
  for +hP: {FD.pieces(E5(e0, e1, e2, e3, e4, r), V(len, t), f) == List.take(&2, L32(), ps, 5n) : LL()}
  FIVE(len, t, ps, e3, e4)

def five(len, t, f, e0, e1, e2, e3, e4, r, ps, hE, hP):
  match ps:
    case Nil{}:
      five.no(len, t, f, e0, e1, e2, e3, e4, r, Nil{}, hP, {==})
    case Con{+q0, Nil{}}:
      five.no(len, t, f, e0, e1, e2, e3, e4, r, Con{q0, Nil{}}, hP, {==})
    case Con{+q0, Con{+q1, Nil{}}}:
      five.no(len, t, f, e0, e1, e2, e3, e4, r, Con{q0, Con{q1, Nil{}}}, hP, {==})
    case Con{+q0, Con{+q1, Con{+q2, Nil{}}}}:
      five.no(len, t, f, e0, e1, e2, e3, e4, r, Con{q0, Con{q1, Con{q2, Nil{}}}}, hP, {==})
    case Con{+q0, Con{+q1, Con{+q2, Con{+q3, Nil{}}}}}:
      five.no(len, t, f, e0, e1, e2, e3, e4, r, Con{q0, Con{q1, Con{q2, Con{q3, Nil{}}}}}, hP, {==})
    case Con{+q0, Con{+q1, Con{+q2, Con{+q3, Con{+q4, +rest}}}}}:
      five.p(len, t, f, e0, e1, e2, e3, e4, r, q0, q1, q2, q3, q4, rest, hE, hP)

# Fewer than five pieces: no ALT field.
law short:
  for +ps: LL()
  for +h5: {has5(List.take(&2, L32(), ps, 5n)) == False{} : Bool}
  {List.get(&2, String, FD.texts(ps), 4n) == None{} : Maybe<&2, String>}

def short(ps, h5):
  match ps:
    case Nil{}:
      {==}
    case Con{+q0, Nil{}}:
      {==}
    case Con{+q0, Con{+q1, Nil{}}}:
      {==}
    case Con{+q0, Con{+q1, Con{+q2, Nil{}}}}:
      {==}
    case Con{+q0, Con{+q1, Con{+q2, Con{+q3, Nil{}}}}}:
      {==}
    case Con{+q0, Con{+q1, Con{+q2, Con{+q3, Con{+q4, +rest}}}}}:
      Empty.absurd({List.get(&2, String, FD.texts(Con{q0, Con{q1, Con{q2, Con{q3, Con{q4, rest}}}}}), 4n) == None{} : Maybe<&2, String>}, P.false_ne_true(Equal.sym(Bool, True{}, False{}, h5)))

# ---------------------------------------------------------------------------
# No comma in the ALT field: at most one ALT
# ---------------------------------------------------------------------------

def ALT1(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32) -> Type:
  {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(LI.TXR(len, t, s, be))))) == False{} : Bool}

# The ALT field's text is text(p), p without a comma.
def alt_p(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32, +p: L32(), +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool},
  +hg: {List.get(&2, String, FD.texts(SPV(len, t, s, be)), 4n) == Some{FD.text(p)} : Maybe<&2, String>},
  +hc: {FD.count(p, 44) == 0n : Nat}) -> ALT1(len, t, s, be):
  +F = B.Rec.fields(LI.TXR(len, t, s, be))
  %Equal.sym(Ss(), F, FD.texts(SPV(len, t, s, be)), flds(len, t, s, be, hn)) :
    {Nat.is_le(2n, List.length(&2, String, String.split(Maybe.default(&2, String, List.get(&2, String, _, 4n), ""), ','))) == False{} : Bool}
  %Equal.sym(Maybe<&2, String>, List.get(&2, String, FD.texts(SPV(len, t, s, be)), 4n), Some{FD.text(p)}, hg) :
    {Nat.is_le(2n, List.length(&2, String, String.split(Maybe.default(&2, String, _, ""), ','))) == False{} : Bool}
  %Equal.sym(Ss(), String.split(FD.text(p), Chr{44}), FD.texts(FD.split(p, 44)), FL.split_text(p, 44)) :
    {Nat.is_le(2n, List.length(&2, String, _)) == False{} : Bool}
  %Equal.sym(Nat, List.length(&2, String, FD.texts(FD.split(p, 44))), List.length(&2, L32(), FD.split(p, 44)), texts_len(FD.split(p, 44))) :
    {Nat.is_le(2n, _) == False{} : Bool}
  %Equal.sym(Nat, List.length(&2, L32(), FD.split(p, 44)), Nat.add(FD.count(p, 44), 1n), FL.split_length(p, 44)) :
    {Nat.is_le(2n, _) == False{} : Bool}
  %Equal.sym(Nat, FD.count(p, 44), 0n, hc) : {Nat.is_le(2n, Nat.add(_, 1n)) == False{} : Bool}
  {==}

# Fewer than five fields: the ALT field is empty.
def alt_short(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32, +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool},
  +hg: {List.get(&2, String, FD.texts(SPV(len, t, s, be)), 4n) == None{} : Maybe<&2, String>}) -> ALT1(len, t, s, be):
  %Equal.sym(Ss(), B.Rec.fields(LI.TXR(len, t, s, be)), FD.texts(SPV(len, t, s, be)), flds(len, t, s, be, hn)) :
    {Nat.is_le(2n, List.length(&2, String, String.split(Maybe.default(&2, String, List.get(&2, String, _, 4n), ""), ','))) == False{} : Bool}
  %Equal.sym(Maybe<&2, String>, List.get(&2, String, FD.texts(SPV(len, t, s, be)), 4n), None{}, hg) :
    {Nat.is_le(2n, List.length(&2, String, String.split(Maybe.default(&2, String, _, ""), ','))) == False{} : Bool}
  {==}

def es_short(+len: U32, +t: AT.Tree<U32>, +s: U32, +be: U32, +es: L32(), +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool},
  +hP: {FD.pieces(es, V(len, t), n(s)) == List.take(&2, L32(), SPV(len, t, s, be), 5n) : LL()},
  +h5: {has5(FD.pieces(es, V(len, t), n(s))) == False{} : Bool}) -> ALT1(len, t, s, be):
  alt_short(len, t, s, be, hn, short(SPV(len, t, s, be),
    Equal.trans(Bool, has5(List.take(&2, L32(), SPV(len, t, s, be), 5n)), has5(FD.pieces(es, V(len, t), n(s))), False{},
      Equal.cong(LL(), Bool, has5, List.take(&2, L32(), SPV(len, t, s, be), 5n), FD.pieces(es, V(len, t), n(s)), Equal.sym(LL(), FD.pieces(es, V(len, t), n(s)), List.take(&2, L32(), SPV(len, t, s, be), 5n), hP)),
      h5)))

# The comma count of the ALT field is zero.
def cm.c(+lf: U32, +k: Nat, +c: Bool, +e: {Nat.is_eq(k, 0n) == c : Bool},
  +hn: {Maybe.is_none(&2, U32, Bool.pick(Maybe<&2, U32>, c, None{}, Some{lf})) == True{} : Bool}) -> {k == 0n : Nat}:
  match c:
    case True{}:
      N.eq_sound(k, 0n, e)
    case False{}:
      Empty.absurd({k == 0n : Nat}, P.false_ne_true(hn))

def cm.k(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +lf: U32, -r: D.Bytes & Nat, cn: SC.CNT(len, t, 0n, a, z, 44, r),
  +hn: {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.comma(r, lf))) == True{} : Bool}) ->
  {FD.count(SC.BS(len, t, a, z), 44) == 0n : Nat}:
  (+k, q) = cn
  (ec, ek) = q
  +hn2 = {%ec : {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.comma(_, lf))) == True{} : Bool};
    hn : {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.comma((C.BT(len, t), k), lf))) == True{} : Bool}}
  Equal.trans(Nat, FD.count(SC.BS(len, t, a, z), 44), k, 0n, Equal.sym(Nat, k, FD.count(SC.BS(len, t, a, z), 44), SC.cnt_val(len, t, a, z, 44, k, ek)),
    cm.c(lf, k, Nat.is_eq(k, 0n), {==}, hn2))

def es_long.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +be: U32, +lf: U32,
  +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool}, +hbl: {Nat.is_lt(n(be), n(len)) == True{} : Bool},
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +r: L32(),
  +hE: {FD.nats(E5(e0, e1, e2, e3, e4, r)) == List.take(&2, Nat, FD.ends(SPV(len, t, s, be), n(s)), 5n) : Ns()},
  +hP: {FD.pieces(E5(e0, e1, e2, e3, e4, r), V(len, t), n(s)) == List.take(&2, L32(), SPV(len, t, s, be), 5n) : LL()},
  +hW: {FD.within(E5(e0, e1, e2, e3, e4, r), n(s), n(be)) == True{} : Bool},
  +hm: {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.es(E5(e0, e1, e2, e3, e4, r), C.BT(len, t), lf))) == True{} : Bool},
  fv: FIVE(len, t, SPV(len, t, s, be), e3, e4)) ->
  ALT1(len, t, s, be):
  (hg, ho) = fv
  +w3 = K.wf_tl(e2, Con{e3, Con{e4, r}}, n(s), n(be), K.wf_tl(e1, Con{e2, Con{e3, Con{e4, r}}}, n(s), n(be), K.wf_tl(e0, Con{e1, Con{e2, Con{e3, Con{e4, r}}}}, n(s), n(be), hW)))
  +h3b = K.wf_hd(e3, Con{e4, r}, n(s), n(be), w3)
  +h4b = K.wf_hd(e4, r, n(s), n(be), K.wf_tl(e3, Con{e4, r}, n(s), n(be), w3))
  +e31 = W.inc_n(len, t, d, e3, hl, LI.ult(e3, len, N.le_lt_trans(n(e3), n(be), n(len), h3b, hbl)))
  +haz = {%Equal.sym(Nat, n((e3 + 1 : U32)), Nat.add(n(e3), 1n), e31) : {Nat.is_le(_, n(e4)) == True{} : Bool};
    %Equal.sym(Nat, n(e4), Nat.add(Nat.add(n(e3), 1n), List.length(&2, U32, P4(len, t, e3, e4))), ho) : {Nat.is_le(Nat.add(n(e3), 1n), _) == True{} : Bool};
    N.le_add_r(Nat.add(n(e3), 1n), List.length(&2, U32, P4(len, t, e3, e4))) : {Nat.is_le(n((e3 + 1 : U32)), n(e4)) == True{} : Bool}}
  +hzl = N.le_trans(n(e4), n(be), n(len), h4b, N.lt_to_le(n(be), n(len), hbl))
  +hc = cm.k(len, t, (e3 + 1 : U32), e4, lf, NS.count(C.BT(len, t), NS.Rg{(e3 + 1 : U32), e4}, 44), SC.count_t(len, t, d, (e3 + 1 : U32), e4, 44, hl, haz, hzl, {==}), hm)
  +hc2 = {%e31 : {FD.count(D.slice(V(len, t), _, Nat.sub(n(e4), _)), 44) == 0n : Nat};
    hc : {FD.count(P4(len, t, e3, e4), 44) == 0n : Nat}}
  alt_p(len, t, s, be, P4(len, t, e3, e4), hn, hg, hc2)

def es_long(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +be: U32, +lf: U32,
  +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool}, +hbl: {Nat.is_lt(n(be), n(len)) == True{} : Bool},
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +r: L32(),
  +hE: {FD.nats(E5(e0, e1, e2, e3, e4, r)) == List.take(&2, Nat, FD.ends(SPV(len, t, s, be), n(s)), 5n) : Ns()},
  +hP: {FD.pieces(E5(e0, e1, e2, e3, e4, r), V(len, t), n(s)) == List.take(&2, L32(), SPV(len, t, s, be), 5n) : LL()},
  +hW: {FD.within(E5(e0, e1, e2, e3, e4, r), n(s), n(be)) == True{} : Bool},
  +hm: {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.es(E5(e0, e1, e2, e3, e4, r), C.BT(len, t), lf))) == True{} : Bool}) ->
  ALT1(len, t, s, be):
  es_long.k(len, t, d, hl, s, be, lf, hn, hbl, e0, e1, e2, e3, e4, r, hE, hP, hW, hm, five(len, t, n(s), e0, e1, e2, e3, e4, r, SPV(len, t, s, be), hE, hP))

def alts.m(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +be: U32, +lf: U32,
  +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool}, +hbl: {Nat.is_lt(n(be), n(len)) == True{} : Bool}, es: L32(),
  +hE: {FD.nats(es) == List.take(&2, Nat, FD.ends(SPV(len, t, s, be), n(s)), 5n) : Ns()},
  +hP: {FD.pieces(es, V(len, t), n(s)) == List.take(&2, L32(), SPV(len, t, s, be), 5n) : LL()},
  +hW: {FD.within(es, n(s), n(be)) == True{} : Bool},
  +hm: {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.es(es, C.BT(len, t), lf))) == True{} : Bool}) ->
  ALT1(len, t, s, be):
  match es:
    case Nil{}:
      es_short(len, t, s, be, Nil{}, hn, hP, {==})
    case Con{+e0, Nil{}}:
      es_short(len, t, s, be, Con{e0, Nil{}}, hn, hP, {==})
    case Con{+e0, Con{+e1, Nil{}}}:
      es_short(len, t, s, be, Con{e0, Con{e1, Nil{}}}, hn, hP, {==})
    case Con{+e0, Con{+e1, Con{+e2, Nil{}}}}:
      es_short(len, t, s, be, Con{e0, Con{e1, Con{e2, Nil{}}}}, hn, hP, {==})
    case Con{+e0, Con{+e1, Con{+e2, Con{+e3, Nil{}}}}}:
      es_short(len, t, s, be, Con{e0, Con{e1, Con{e2, Con{e3, Nil{}}}}}, hn, hP, {==})
    case Con{+e0, Con{+e1, Con{+e2, Con{+e3, Con{+e4, +r}}}}}:
      es_long(len, t, d, hl, s, be, lf, hn, hbl, e0, e1, e2, e3, e4, r, hE, hP, hW, hm)

# The five ends NS.multi reads: no comma between the fourth and the fifth.
law alts_es:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +s: U32
  for +be: U32
  for +lf: U32
  for +hsb: {U32.is_le(s, be) == True{} : Bool}
  for +hn: {Nat.is_le(n(s), n(be)) == True{} : Bool}
  for +hbl: {Nat.is_lt(n(be), n(len)) == True{} : Bool}
  for +es: L32()
  for +hes: {ES5(len, t, s, be) == es : L32()}
  for +hm: {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.es(es, C.BT(len, t), lf))) == True{} : Bool}
  ALT1(len, t, s, be)

def alts_es(len, t, d, hl, s, be, lf, hsb, hn, hbl, es, hes, hm):
  +hbe = N.lt_to_le(n(be), n(len), hbl)
  +CV = FL.cut_view(C.BT(len, t), d, s, be, 9, 5n, hl, hsb, hbe, {==})
  +CE = FL.cut_ends(C.BT(len, t), d, s, be, 9, 5n, hl, hsb, hbe, {==})
  +CB = FL.cut_bounds(C.BT(len, t), d, s, be, 9, 5n, hl, hsb, hbe, {==})
  +hP = {%hes : {FD.pieces(_, V(len, t), n(s)) == List.take(&2, L32(), SPV(len, t, s, be), 5n) : LL()}; CV : {FD.pieces(es, V(len, t), n(s)) == List.take(&2, L32(), SPV(len, t, s, be), 5n) : LL()}}
  +hE = {%hes : {FD.nats(_) == List.take(&2, Nat, FD.ends(SPV(len, t, s, be), n(s)), 5n) : Ns()}; CE : {FD.nats(es) == List.take(&2, Nat, FD.ends(SPV(len, t, s, be), n(s)), 5n) : Ns()}}
  +hW = {%hes : {FD.within(_, n(s), n(be)) == True{} : Bool}; CB : {FD.within(es, n(s), n(be)) == True{} : Bool}}
  alts.m(len, t, d, hl, s, be, lf, hn, hbl, es, hE, hP, hW, hm)

# ---------------------------------------------------------------------------
# multi's None: the line stays whole
# ---------------------------------------------------------------------------

# At most one ALT: B.Rec.parts leaves the line whole.
def parts_whole(+defs: B.Defs, +o: B.Opts, +body: String,
  +h: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == False{} : Bool}) ->
  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}:
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      +fs = B.Rec.fields(body)
      +A = Bool.and(sp, Bool.not(B.Rec.malformed(fs)))
      %Equal.sym(Bool, Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))), False{}, h) :
        {B.Rec.parts.if(Bool.and(A, _), B.Text.has_cr(body), defs, o0, fs) == B.Whole{} : B.Parts}
      %Equal.sym(Bool, Bool.and(A, False{}), False{}, N.and_false_r(A)) :
        {B.Rec.parts.if(_, B.Text.has_cr(body), defs, o0, fs) == B.Whole{} : B.Parts}
      {==}

# The fast path's test: without -m, or when multi answers None.
def MW(+o: B.Opts, +len: U32, +t: AT.Tree<U32>, +s: U32) -> Bool:
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      Bool.not(sp) || Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), s)))

def mw.sp(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +defs: B.Defs,
  +st: Bool, +w: Nat, +o0: Bool, +args: Ss(), +s: U32, +lf: U32,
  +hsl: {Nat.is_le(n(s), n(lf)) == True{} : Bool}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +hfst: {n(lf) == D.first(V(len, t), n(s), n(len), 10) : Nat}, +sp: Bool,
  +hmw: {MW(B.Opts{st, w, sp, o0, args}, len, t, s) == True{} : Bool}) ->
  {B.Rec.parts(defs, B.Opts{st, w, sp, o0, args}, LI.TXR(len, t, s, LI.BE(len, t, s, lf))) == B.Whole{} : B.Parts}:
  match sp:
    case False{}:
      {==}
    case True{}:
      +be = LI.BE(len, t, s, lf)
      +hsle = DR.be_lo.k(len, t, s, lf, hsl, U32.is_lt(s, lf), {==})
      +hbl = N.le_lt_trans(n(be), n(lf), n(len), DR.be_hi.k(len, t, s, lf, U32.is_lt(s, lf), {==}), hlf)
      +hsb = Equal.trans(Bool, U32.is_le(s, be), Nat.is_le(n(s), n(be)), True{}, U.is_le_to_nat(s, be), hsle)
      +hm = {%multi_es(len, t, d, hl, s, lf, hsl, hlf, hfst) : {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, _)) == True{} : Bool};
        hmw : {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi.es(ES5(len, t, s, be), C.BT(len, t), lf))) == True{} : Bool}}
      parts_whole(defs, B.Opts{st, w, True{}, o0, args}, LI.TXR(len, t, s, be),
        alts_es(len, t, d, hl, s, be, lf, hsb, hsle, hbl, ES5(len, t, s, be), {==}, hm))

# The line s .. lf (its first LF at lf): when the fast path's test passes,
# B.Rec.parts leaves its body whole.
law mw_whole:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +defs: B.Defs
  for +o: B.Opts
  for +s: U32
  for +lf: U32
  for +hsl: {Nat.is_le(n(s), n(lf)) == True{} : Bool}
  for +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  for +hfst: {n(lf) == D.first(V(len, t), n(s), n(len), 10) : Nat}
  for +hmw: {MW(o, len, t, s) == True{} : Bool}
  {B.Rec.parts(defs, o, LI.TXR(len, t, s, LI.BE(len, t, s, lf))) == B.Whole{} : B.Parts}

def mw_whole(len, t, d, hl, defs, o, s, lf, hsl, hlf, hfst, hmw):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      mw.sp(len, t, d, hl, defs, st, w, o0, args, s, lf, hsl, hlf, hfst, sp, hmw)

# ---------------------------------------------------------------------------
# multi hands the buffer back
# ---------------------------------------------------------------------------

# A Some answer is the LF at lf, below len.
def MV(m: Maybe<&2, U32>, +lf: U32, +len: U32) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+x}:
      Nat.is_eq(n(x), n(lf)) && Nat.is_lt(n(x), n(len))

def MP(+len: U32, +t: AT.Tree<U32>, -r: D.Bytes & Maybe<&2, U32>, +lf: U32) -> Type:
  {r == (C.BT(len, t), Pair.snd(D.Bytes, Maybe<&2, U32>, r)) : D.Bytes & Maybe<&2, U32>} &
  {MV(Pair.snd(D.Bytes, Maybe<&2, U32>, r), lf, len) == True{} : Bool}

def mv.c(+len: U32, +t: AT.Tree<U32>, +lf: U32, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}, +c: Bool) ->
  MP(len, t, (C.BT(len, t), Bool.pick(Maybe<&2, U32>, c, None{}, Some{lf})), lf):
  match c:
    case True{}:
      ({==}, {==})
    case False{}:
      ({==}, {%Equal.sym(Bool, Nat.is_eq(n(lf), n(lf)), True{}, N.eq_refl(n(lf))) : {Bool.and(_, Nat.is_lt(n(lf), n(len))) == True{} : Bool}; hlf : {Bool.and(Nat.is_eq(n(lf), n(lf)), Nat.is_lt(n(lf), n(len))) == True{} : Bool}})

def mp_cnt(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +lf: U32, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}, -r: D.Bytes & Nat, cn: SC.CNT(len, t, 0n, a, z, 44, r)) ->
  MP(len, t, NS.multi.comma(r, lf), lf):
  (+k, q) = cn
  (ec, ek) = q
  %Equal.sym(D.Bytes & Nat, r, (C.BT(len, t), k), ec) : MP(len, t, NS.multi.comma(_, lf), lf)
  mv.c(len, t, lf, hlf, Nat.is_eq(k, 0n))
def ep.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +be: U32, +lf: U32,
  +hbl: {Nat.is_lt(n(be), n(len)) == True{} : Bool},
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +r: L32(),
  +hW: {FD.within(E5(e0, e1, e2, e3, e4, r), n(s), n(be)) == True{} : Bool},
  +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  fv: FIVE(len, t, SPV(len, t, s, be), e3, e4)) ->
  MP(len, t, NS.multi.es(E5(e0, e1, e2, e3, e4, r), C.BT(len, t), lf), lf):
  (hg, ho) = fv
  +w3 = K.wf_tl(e2, Con{e3, Con{e4, r}}, n(s), n(be), K.wf_tl(e1, Con{e2, Con{e3, Con{e4, r}}}, n(s), n(be), K.wf_tl(e0, Con{e1, Con{e2, Con{e3, Con{e4, r}}}}, n(s), n(be), hW)))
  +h3b = K.wf_hd(e3, Con{e4, r}, n(s), n(be), w3)
  +h4b = K.wf_hd(e4, r, n(s), n(be), K.wf_tl(e3, Con{e4, r}, n(s), n(be), w3))
  +e31 = W.inc_n(len, t, d, e3, hl, LI.ult(e3, len, N.le_lt_trans(n(e3), n(be), n(len), h3b, hbl)))
  +haz = {%Equal.sym(Nat, n((e3 + 1 : U32)), Nat.add(n(e3), 1n), e31) : {Nat.is_le(_, n(e4)) == True{} : Bool};
    %Equal.sym(Nat, n(e4), Nat.add(Nat.add(n(e3), 1n), List.length(&2, U32, P4(len, t, e3, e4))), ho) : {Nat.is_le(Nat.add(n(e3), 1n), _) == True{} : Bool};
    N.le_add_r(Nat.add(n(e3), 1n), List.length(&2, U32, P4(len, t, e3, e4))) : {Nat.is_le(n((e3 + 1 : U32)), n(e4)) == True{} : Bool}}
  +hzl = N.le_trans(n(e4), n(be), n(len), h4b, N.lt_to_le(n(be), n(len), hbl))
  mp_cnt(len, t, (e3 + 1 : U32), e4, lf, hlf, NS.count(C.BT(len, t), NS.Rg{(e3 + 1 : U32), e4}, 44), SC.count_t(len, t, d, (e3 + 1 : U32), e4, 44, hl, haz, hzl, {==}))

def pair.m(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +be: U32, +lf: U32,
  +hbl: {Nat.is_lt(n(be), n(len)) == True{} : Bool}, es: L32(),
  +hE: {FD.nats(es) == List.take(&2, Nat, FD.ends(SPV(len, t, s, be), n(s)), 5n) : Ns()},
  +hP: {FD.pieces(es, V(len, t), n(s)) == List.take(&2, L32(), SPV(len, t, s, be), 5n) : LL()},
  +hW: {FD.within(es, n(s), n(be)) == True{} : Bool},
  +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) ->
  MP(len, t, NS.multi.es(es, C.BT(len, t), lf), lf):
  match es:
    case Nil{}:
      ({==}, {==})
    case Con{+e0, Nil{}}:
      ({==}, {==})
    case Con{+e0, Con{+e1, Nil{}}}:
      ({==}, {==})
    case Con{+e0, Con{+e1, Con{+e2, Nil{}}}}:
      ({==}, {==})
    case Con{+e0, Con{+e1, Con{+e2, Con{+e3, Nil{}}}}}:
      ({==}, {==})
    case Con{+e0, Con{+e1, Con{+e2, Con{+e3, Con{+e4, +r}}}}}:
      ep.k(len, t, d, hl, s, be, lf, hbl, e0, e1, e2, e3, e4, r, hW, hlf, five(len, t, n(s), e0, e1, e2, e3, e4, r, SPV(len, t, s, be), hE, hP))

def pair_es(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +be: U32, +lf: U32,
  +hsb: {U32.is_le(s, be) == True{} : Bool}, +hbl: {Nat.is_lt(n(be), n(len)) == True{} : Bool}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) ->
  MP(len, t, NS.multi.es(ES5(len, t, s, be), C.BT(len, t), lf), lf):
  +es = ES5(len, t, s, be)
  +hbe = N.lt_to_le(n(be), n(len), hbl)
  pair.m(len, t, d, hl, s, be, lf, hbl, es,
    FL.cut_ends(C.BT(len, t), d, s, be, 9, 5n, hl, hsb, hbe, {==}),
    FL.cut_view(C.BT(len, t), d, s, be, 9, 5n, hl, hsb, hbe, {==}),
    FL.cut_bounds(C.BT(len, t), d, s, be, 9, 5n, hl, hsb, hbe, {==}), hlf)

def mp.lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +j: U32,
  +hsj: {Nat.is_le(n(s), n(j)) == True{} : Bool}, +c: Bool, +e: {U32.is_lt(j, len) == c : Bool}) ->
  MP(len, t, NS.multi.lf.if(c, C.BT(len, t), s, j), j):
  match c:
    case False{}:
      ({==}, {==})
    case True{}:
      +hlf = Equal.trans(Bool, Nat.is_lt(n(j), n(len)), U32.is_lt(j, len), True{}, Equal.sym(Bool, U32.is_lt(j, len), Nat.is_lt(n(j), n(len)), U.is_lt_to_nat(j, len)), e)
      +be = LI.BE(len, t, s, j)
      +hsle = DR.be_lo.k(len, t, s, j, hsj, U32.is_lt(s, j), {==})
      +hbl = N.le_lt_trans(n(be), n(j), n(len), DR.be_hi.k(len, t, s, j, U32.is_lt(s, j), {==}), hlf)
      +hsb = Equal.trans(Bool, U32.is_le(s, be), Nat.is_le(n(s), n(be)), True{}, U.is_le_to_nat(s, be), hsle)
      %DR.at_s(len, t, Bool.pick(U32, U32.is_lt(s, j), (j - 1 : U32), j)) : MP(len, t, NS.multi.cr(_, s, j), j)
      %Equal.sym(D.Bytes & L32(), NS.cut.ends(C.BT(len, t), s, be, 9, 5n), FC.cut(C.BT(len, t), s, be, 9, 5n), K.ends_eq(len, t, d, s, be, 9, 5n, hl, hsb, N.lt_to_le(n(be), n(len), hbl), {==})) :
        MP(len, t, NS.multi.cut(_, j), j)
      %Equal.sym(D.Bytes & L32(), FC.cut(C.BT(len, t), s, be, 9, 5n), (C.BT(len, t), ES5(len, t, s, be)), FL.cut_pair(C.BT(len, t), s, be, 9, 5n)) :
        MP(len, t, NS.multi.cut(_, j), j)
      pair_es(len, t, d, hl, s, be, j, hsb, hbl, hlf)

# multi hands back the buffer it was given.
law multi_pair:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +s: U32
  for +hs: {U32.is_le(s, len) == True{} : Bool}
  MP(len, t, NS.multi(C.BT(len, t), s), Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), s, len, 10)))

def multi_pair(len, t, d, hl, s, hs):
  +j = Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), s, len, 10))
  +hj = Equal.trans(Nat, n(j), n(Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), s, len, 10))), D.first(V(len, t), n(s), n(len), 10),
    Equal.cong(D.Bytes & U32, Nat, r => n(Pair.snd(D.Bytes, U32, r)), F.find(C.BT(len, t), s, len, 10), BY.find(C.BT(len, t), s, len, 10), FE.find_eq(C.BT(len, t), d, s, len, 10, hl, hs, N.le_refl(n(len)), {==})),
    PF.find_view_t(len, t, d, s, len, 10, hl, hs, N.le_refl(n(len)), {==}))
  +hsj = {%Equal.sym(Nat, n(j), D.first(V(len, t), n(s), n(len), 10), hj) : {Nat.is_le(n(s), _) == True{} : Bool}; N.le_add_r(n(s), D.run_len(D.slice(V(len, t), n(s), Nat.sub(n(len), n(s))), 10)) : {Nat.is_le(n(s), n(j)) == True{} : Bool}}
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s, len, 10), (C.BT(len, t), j), FE.find_pair(C.BT(len, t), s, len, 10)) : MP(len, t, NS.multi.lf(s, _, len), j)
  mp.lf(len, t, d, hl, s, j, hsj, U32.is_lt(j, len), {==})
