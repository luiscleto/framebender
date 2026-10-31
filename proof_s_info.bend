import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as AL
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_ws.bend as S
import ./proof_s_cut.bend as K
import ./proof_s_scan.bend as SC
import ./proof_s_read.bend as RD
import ./proof_s_vals.bend as VL
import ./proof_s_gt.bend as GT
import ./proof_s_gtspec.bend as G
import ./proof_s_kinds.bend as KD
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_list.bend as BL
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# One INFO entry in the record for ALT i (norm_split.bend's info.one on the
# kind ikinds found) writes what B.Info.split.num gives. Every variable is
# reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def Ss() -> Data:
  List<&2, String>

def Tags() -> Data:
  List<&2, B.Tag>

def TXR(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> String:
  WT.TX(len, t, NS.Rg{a, z})

def J(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> U32:
  KD.JE(len, t, a, z)

# ---------------------------------------------------------------------------
# The entry's text: key, '=', value
# ---------------------------------------------------------------------------

def key_eq(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {B.Info.key(TXR(len, t, a, z)) == TXR(len, t, a, J(len, t, a, z)) : String}:
  +j = J(len, t, a, z)
  +haj = SC.j_lo(len, t, d, a, z, 61, h, haz, hzl, {==})
  %Equal.sym(Ss(), String.split(TXR(len, t, a, z), '='), K.CHS(K.SP(len, t, a, z, 61)), VL.split_chs(len, t, a, z, 61, haz)) : {B.Rec.field(_, 0n) == TXR(len, t, a, j) : String}
  %Equal.sym(List<&2, List<&2, U32>>, K.SP(len, t, a, z, 61), Con{SC.BS(len, t, a, j), SC.TS(len, t, j, z, 61)}, SC.sp_first(len, t, d, a, z, 61, h, haz, hzl, {==})) : {B.Rec.field(K.CHS(_), 0n) == TXR(len, t, a, j) : String}
  Equal.sym(String, TXR(len, t, a, j), NR.chars(SC.BS(len, t, a, j)), RD.tx_eq(len, t, a, j, haj))

def sne.k(+b: Bool, +x: Nat, +y: Nat, +z: Nat, +hx: {Nat.is_le(x, y) == True{} : Bool}, +hz: {Nat.is_le(x, z) == True{} : Bool},
  +hne: {Nat.is_eq(y, z) == False{} : Bool}, +hb: {Nat.is_eq(Nat.sub(y, x), Nat.sub(z, x)) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +e = N.eq_sound(Nat.sub(y, x), Nat.sub(z, x), hb)
      +ey = Equal.trans(Nat, y, Nat.add(x, Nat.sub(z, x)), z,
        Equal.trans(Nat, y, Nat.add(x, Nat.sub(y, x)), Nat.add(x, Nat.sub(z, x)), Equal.sym(Nat, Nat.add(x, Nat.sub(y, x)), y, N.le_sub_add(x, y, hx)),
          Equal.cong(Nat, Nat, q => Nat.add(x, q), Nat.sub(y, x), Nat.sub(z, x), e)),
        N.le_sub_add(x, z, hz))
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_eq(z, z), True{},
        {%ey : {False{} == Nat.is_eq(_, z) : Bool}; Equal.sym(Bool, Nat.is_eq(y, z), False{}, hne) : {False{} == Nat.is_eq(z, z) : Bool}}, N.eq_refl(z))))

def sub_ne(+x: Nat, +y: Nat, +z: Nat, +hx: {Nat.is_le(x, y) == True{} : Bool}, +hz: {Nat.is_le(x, z) == True{} : Bool},
  +hne: {Nat.is_eq(y, z) == False{} : Bool}) -> {Nat.is_eq(Nat.sub(y, x), Nat.sub(z, x)) == False{} : Bool}:
  sne.k(Nat.is_eq(Nat.sub(y, x), Nat.sub(z, x)), x, y, z, hx, hz, hne, {==})

def A1(+x: U32) -> U32:
  (x + 1 : U32)

# The key is the whole entry exactly when it has no '='.
def nv.k(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_eq(z, J(len, t, a, z)) == c : Bool}) ->
  {D.list_eq(W.SL(len, t, a, J(len, t, a, z)), W.SL(len, t, a, z)) == c : Bool}:
  match c:
    case True{}:
      +j = J(len, t, a, z)
      %Equal.sym(U32, z, j, U.is_eq_true(z, j, hc)) : {D.list_eq(W.SL(len, t, a, j), W.SL(len, t, a, _)) == True{} : Bool}
      BL.list_eq_refl(W.SL(len, t, a, j))
    case False{}:
      +j = J(len, t, a, z)
      +haj = SC.j_lo(len, t, d, a, z, 61, h, haz, hzl, {==})
      +hjz = SC.j_hi(len, t, d, a, z, 61, h, haz, hzl, {==})
      +hne = Equal.trans(Bool, Nat.is_eq(n(j), n(z)), Nat.is_eq(n(z), n(j)), False{}, N.eq_comm(n(j), n(z)),
        Equal.trans(Bool, Nat.is_eq(n(z), n(j)), U32.is_eq(z, j), False{}, Equal.sym(Bool, U32.is_eq(z, j), Nat.is_eq(n(z), n(j)), U.is_eq_to_nat(z, j)), hc))
      +l1 = Equal.trans(Nat, List.length(&2, U32, W.SL(len, t, a, j)), n((j - a : U32)), Nat.sub(n(j), n(a)),
        AL.slice_len(W.V(len, t), n(a), n((j - a : U32)), %AL.len_x(len, t, d, h) : {Nat.is_le(Nat.add(n(a), n((j - a : U32))), _) == True{} : Bool}; W.pv_put(len, a, j, W.pv_mk(len, a, j, haj, N.le_trans(n(j), n(z), n(len), hjz, hzl)))),
        W.nsub(a, j, haj))
      +l2 = Equal.trans(Nat, List.length(&2, U32, W.SL(len, t, a, z)), n((z - a : U32)), Nat.sub(n(z), n(a)),
        AL.slice_len(W.V(len, t), n(a), n((z - a : U32)), %AL.len_x(len, t, d, h) : {Nat.is_le(Nat.add(n(a), n((z - a : U32))), _) == True{} : Bool}; W.pv_put(len, a, z, W.pv_mk(len, a, z, haz, hzl))),
        W.nsub(a, z, haz))
      AL.list_eq_len(W.SL(len, t, a, j), W.SL(len, t, a, z),
        %Equal.sym(Nat, List.length(&2, U32, W.SL(len, t, a, j)), Nat.sub(n(j), n(a)), l1) : {Nat.is_eq(_, List.length(&2, U32, W.SL(len, t, a, z))) == False{} : Bool};
        %Equal.sym(Nat, List.length(&2, U32, W.SL(len, t, a, z)), Nat.sub(n(z), n(a)), l2) : {Nat.is_eq(Nat.sub(n(j), n(a)), _) == False{} : Bool};
        sub_ne(n(a), n(j), n(z), haj, haz, hne))

def noval_eq(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {String.eq(TXR(len, t, a, J(len, t, a, z)), TXR(len, t, a, z)) == U32.is_eq(z, J(len, t, a, z)) : Bool}:
  %Equal.sym(Bool, String.eq(TXR(len, t, a, J(len, t, a, z)), TXR(len, t, a, z)), D.list_eq(W.SL(len, t, a, J(len, t, a, z)), W.SL(len, t, a, z)), RD.seq(W.SL(len, t, a, J(len, t, a, z)), W.SL(len, t, a, z))) : {_ == U32.is_eq(z, J(len, t, a, z)) : Bool}
  nv.k(U32.is_eq(z, J(len, t, a, z)), len, t, d, a, z, h, haz, hzl, {==})

def drop0(+v: String) -> {String.drop(v, 0n) == v : String}:
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      {==}

law drop_app:
  for +us: String
  for +c: Char
  for +v: String
  {String.drop(String.append(us, SCon{c, v}), Nat.add(String.length(us), 1n)) == v : String}

def drop_app(us, c, v):
  match us:
    case SNil{}:
      drop0(v)
    case SCon{+h, +r}:
      drop_app(r, c, v)

# The value: the text after the first '='.
def val_eq(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(J(len, t, a, z)), n(z)) == True{} : Bool}) ->
  {String.drop(TXR(len, t, a, z), Nat.add(String.length(TXR(len, t, a, J(len, t, a, z))), 1n)) == TXR(len, t, A1(J(len, t, a, z)), z) : String}:
  +j = J(len, t, a, z)
  +haj = SC.j_lo(len, t, d, a, z, 61, h, haz, hzl, {==})
  %Equal.sym(String, TXR(len, t, a, z), String.append(TXR(len, t, a, j), SCon{Chr{C.AT(len, t, j)}, TXR(len, t, A1(j), z)}), GT.txr_sep(len, t, d, a, j, z, h, haj, hjz, hzl)) :
    {String.drop(_, Nat.add(String.length(TXR(len, t, a, j)), 1n)) == TXR(len, t, A1(j), z) : String}
  drop_app(TXR(len, t, a, j), Chr{C.AT(len, t, j)}, TXR(len, t, A1(j), z))

def msv(+m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{+x}:
      x
    case None{}:
      0

# The key and '='.
def keq(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(J(len, t, a, z)), n(z)) == True{} : Bool}) ->
  {TXR(len, t, a, A1(J(len, t, a, z))) == String.append(TXR(len, t, a, J(len, t, a, z)), "=") : String}:
  +j = J(len, t, a, z)
  +haj = SC.j_lo(len, t, d, a, z, 61, h, haz, hzl, {==})
  +hjl = N.lt_le_trans(n(j), n(z), n(len), hjz, hzl)
  +hju = Equal.trans(Bool, U32.is_lt(j, len), Nat.is_lt(n(j), n(len)), True{}, U.is_lt_to_nat(j, len), hjl)
  +ej1 = AL.inc_len(len, t, d, j, h, hjl)
  +hjj = {%Equal.sym(Nat, n(A1(j)), Nat.add(n(j), 1n), ej1) : {Nat.is_le(n(j), _) == True{} : Bool}; N.le_add_r(n(j), 1n) : {Nat.is_le(n(j), n(A1(j))) == True{} : Bool}}
  +ex = Equal.cong(Maybe<&2, U32>, U32, m => msv(m), Some{C.AT(len, t, j)}, Some{61},
    Equal.trans(Maybe<&2, U32>, Some{C.AT(len, t, j)}, List.get(&2, U32, W.V(len, t), n(j)), Some{61},
      C.at_view_t(len, t, d, j, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hjl),
      SC.j_hit(len, t, d, a, z, 61, h, haz, hzl, {==}, hjz)))
  %Equal.sym(String, NR.chars(W.SL(len, t, a, A1(j))), String.append(NR.chars(W.SL(len, t, a, j)), NR.chars(W.SL(len, t, j, A1(j)))), WT.tx_app(len, t, a, j, A1(j), haj, hjj)) :
    {_ == String.append(TXR(len, t, a, j), "=") : String}
  %Equal.sym(List<&2, U32>, W.SL(len, t, j, A1(j)), [C.AT(len, t, j)], WT.sl_one(len, t, d, j, h, hju)) :
    {String.append(TXR(len, t, a, j), NR.chars(_)) == String.append(TXR(len, t, a, j), "=") : String}
  %Equal.sym(U32, C.AT(len, t, j), 61, ex) : {String.append(TXR(len, t, a, j), NR.chars([_])) == String.append(TXR(len, t, a, j), "=") : String}
  {==}

# ---------------------------------------------------------------------------
# info.one
# ---------------------------------------------------------------------------

def SEQ(+KY: String, +V0: Maybe<&2, String>) -> B.Got:
  B.Got.cat(B.Got{KY}, "=", B.Got.of(V0, B.BadCount{}))

def ival.k(+V0: Maybe<&2, String>, +KY: String, +TXa: String,
  +hiss: {VL.ISS(V0) == True{} : Bool}, +ek: {TXa == String.append(KY, "=") : String}) ->
  ({G.GOK(SEQ(KY, V0)) == True{} : Bool} & {String.append(TXa, VL.STR(V0)) == G.GSTR(SEQ(KY, V0)) : String}):
  match V0:
    case Some{+s}:
      ({==}, {%Equal.sym(String, TXa, String.append(KY, "="), ek) : {String.append(_, s) == String.append(KY, String.append("=", s)) : String}; MN.str_assoc(KY, "=", s) : {String.append(TXa, s) == String.append(KY, String.append("=", s)) : String}})
    case None{}:
      Empty.absurd(({G.GOK(SEQ(KY, None{})) == True{} : Bool} & {String.append(TXa, "") == G.GSTR(SEQ(KY, None{})) : String}), P.false_ne_true(hiss))

# An entry with a value for a per-allele tag (Number num): "key=" then the
# record's values.
def info.val(+num: B.Num, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +nalt: Nat, +i: Nat, +a: U32, +z: U32, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(J(len, t, a, z)), n(z)) == True{} : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.info.one(w, NS.IVal{NS.Rg{a, z}, NS.Rg{A1(J(len, t, a, z)), z}, num}, nalt, i), m0,
    G.GSTR(SEQ(TXR(len, t, a, J(len, t, a, z)), B.Vals.split(num, nalt, Some{2n}, i, String.drop(TXR(len, t, a, z), Nat.add(String.length(TXR(len, t, a, J(len, t, a, z))), 1n))))),
    G.GOK(SEQ(TXR(len, t, a, J(len, t, a, z)), B.Vals.split(num, nalt, Some{2n}, i, String.drop(TXR(len, t, a, z), Nat.add(String.length(TXR(len, t, a, J(len, t, a, z))), 1n)))))):
  +j = J(len, t, a, z)
  +j1 = A1(j)
  +KY = TXR(len, t, a, j)
  +V0 = VL.VSPL(num, nalt, Some{2n}, i, len, t, NS.Rg{j1, z})
  +haj = SC.j_lo(len, t, d, a, z, 61, hl, haz, hzl, {==})
  +hjl = N.lt_le_trans(n(j), n(z), n(len), hjz, hzl)
  +ej1 = AL.inc_len(len, t, d, j, hl, hjl)
  +hjj = {%Equal.sym(Nat, n(j1), Nat.add(n(j), 1n), ej1) : {Nat.is_le(n(j), _) == True{} : Bool}; N.le_add_r(n(j), 1n) : {Nat.is_le(n(j), n(j1)) == True{} : Bool}}
  +hj1z = SC.j1_le(len, t, d, j, z, hl, hzl, hjz)
  +hpk = W.pv_mk(len, a, j1, N.le_trans(n(a), n(j), n(j1), haj, hjj), N.le_trans(n(j1), n(z), n(len), hj1z, hzl))
  +hpv = W.pv_mk(len, j1, z, hj1z, hzl)
  %Equal.sym(String, String.drop(TXR(len, t, a, z), Nat.add(String.length(KY), 1n)), TXR(len, t, j1, z), val_eq(len, t, d, a, z, hl, haz, hzl, hjz)) :
    S.WS(len, t, NS.info.one(w, NS.IVal{NS.Rg{a, z}, NS.Rg{j1, z}, num}, nalt, i), m0,
      G.GSTR(SEQ(KY, B.Vals.split(num, nalt, Some{2n}, i, _))), G.GOK(SEQ(KY, B.Vals.split(num, nalt, Some{2n}, i, _))))
  S.ws_imp(len, t, NS.vals(NS.cpr(w, NS.Rg{a, j1}), num, nalt, Some{2n}, i, NS.Rg{j1, z}), m0,
    String.append(WT.TX(len, t, NS.Rg{a, j1}), VL.STR(V0)), Bool.and(True{}, VL.ISS(V0)), G.GSTR(SEQ(KY, V0)), G.GOK(SEQ(KY, V0)),
    hg => ival.k(V0, KY, WT.TX(len, t, NS.Rg{a, j1}), hg, keq(len, t, d, a, z, hl, haz, hzl, hjz)),
    S.ws_seq(len, t, NS.cpr(w, NS.Rg{a, j1}), v => NS.vals(v, num, nalt, Some{2n}, i, NS.Rg{j1, z}), m0,
      WT.TX(len, t, NS.Rg{a, j1}), VL.STR(V0), True{}, VL.ISS(V0),
      S.ws_cpr(len, t, d, hl, NS.Rg{a, j1}, hpk, w, m0, r),
      +m1 => r1 => VL.vals_t(len, t, d, hl, j1, z, hpv, num, nalt, Some{2n}, i, NS.cpr(w, NS.Rg{a, j1}), m1, r1)))

def ISN(+tags: Tags(), +nalt: Nat, +i: Nat, +e: String) -> B.Got:
  B.Info.split.num(B.Tags.find(tags, B.Info.key(e)), e, nalt, i)

def ISNb(+b: Bool, +M: Maybe<&2, B.Num>, +KY: String, +e: String, +nalt: Nat, +i: Nat) -> B.Got:
  Bool.pick(B.Got, b, Bool.pick(B.Got, B.Num.per_allele(M), B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(M, KY, e, nalt, i))

def isn_eq(+len: U32, +t: AT.Tree<U32>, +d: Nat, +tags: Tags(), +nalt: Nat, +i: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {ISN(tags, nalt, i, TXR(len, t, a, z)) == ISNb(U32.is_eq(z, J(len, t, a, z)), B.Tags.find(tags, TXR(len, t, a, J(len, t, a, z))), TXR(len, t, a, J(len, t, a, z)), TXR(len, t, a, z), nalt, i) : B.Got}:
  +E = TXR(len, t, a, z)
  +KY = TXR(len, t, a, J(len, t, a, z))
  +R = ISNb(U32.is_eq(z, J(len, t, a, z)), B.Tags.find(tags, KY), KY, E, nalt, i)
  %Equal.sym(String, B.Info.key(E), KY, key_eq(len, t, d, a, z, h, haz, hzl)) :
    {Bool.pick(B.Got, String.eq(_, E), Bool.pick(B.Got, B.Num.per_allele(B.Tags.find(tags, _)), B.Refuse{B.BadCount{}}, B.Got{E}), B.Info.split.eq(B.Tags.find(tags, _), _, E, nalt, i)) == R : B.Got}
  %Equal.sym(Bool, String.eq(KY, E), U32.is_eq(z, J(len, t, a, z)), noval_eq(len, t, d, a, z, h, haz, hzl)) :
    {Bool.pick(B.Got, _, Bool.pick(B.Got, B.Num.per_allele(B.Tags.find(tags, KY)), B.Refuse{B.BadCount{}}, B.Got{E}), B.Info.split.eq(B.Tags.find(tags, KY), KY, E, nalt, i)) == R : B.Got}
  {==}

def info.pa(+pa: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +nalt: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.info.one(w, Bool.pick(NS.Ik, pa, NS.IBad{}, NS.IKeep{NS.Rg{a, z}}), nalt, i), m0,
    G.GSTR(Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{TXR(len, t, a, z)})), G.GOK(Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{TXR(len, t, a, z)}))):
  match pa:
    case True{}:
      S.ws_fail(len, t, "", False{}, w, m0, r)
    case False{}:
      S.ws_cpr(len, t, d, hl, NS.Rg{a, z}, hpz, w, m0, r)

def info.m(+M: Maybe<&2, B.Num>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +nalt: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hjz: {Nat.is_lt(n(J(len, t, a, z)), n(z)) == True{} : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.info.one(w, NS.ikind.num(M, NS.Rg{a, z}, NS.Rg{A1(J(len, t, a, z)), z}), nalt, i), m0,
    G.GSTR(B.Info.split.eq(M, TXR(len, t, a, J(len, t, a, z)), TXR(len, t, a, z), nalt, i)), G.GOK(B.Info.split.eq(M, TXR(len, t, a, J(len, t, a, z)), TXR(len, t, a, z), nalt, i))):
  match M:
    case None{}:
      S.ws_fail(len, t, "", False{}, w, m0, r)
    case Some{B.NumUnknown{}}:
      S.ws_fail(len, t, "", False{}, w, m0, r)
    case Some{B.NumOther{}}:
      S.ws_cpr(len, t, d, hl, NS.Rg{a, z}, hpz, w, m0, r)
    case Some{B.NumA{}}:
      info.val(B.NumA{}, len, t, d, hl, nalt, i, a, z, W.pv_a(len, a, z, hpz), W.pv_z(len, a, z, hpz), hjz, w, m0, r)
    case Some{B.NumR{}}:
      info.val(B.NumR{}, len, t, d, hl, nalt, i, a, z, W.pv_a(len, a, z, hpz), W.pv_z(len, a, z, hpz), hjz, w, m0, r)
    case Some{B.NumG{}}:
      info.val(B.NumG{}, len, t, d, hl, nalt, i, a, z, W.pv_a(len, a, z, hpz), W.pv_z(len, a, z, hpz), hjz, w, m0, r)

def U32EQ(+x: U32, +y: U32) -> {U32.is_eq(x, y) == U32.is_eq(y, x) : Bool}:
  %Equal.sym(Bool, U32.is_eq(x, y), Nat.is_eq(n(x), n(y)), U.is_eq_to_nat(x, y)) : {_ == U32.is_eq(y, x) : Bool}
  %Equal.sym(Bool, U32.is_eq(y, x), Nat.is_eq(n(y), n(x)), U.is_eq_to_nat(y, x)) : {Nat.is_eq(n(x), n(y)) == _ : Bool}
  N.eq_comm(n(x), n(y))

def info.b(+b: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +nalt: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hb: {U32.is_eq(z, J(len, t, a, z)) == b : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.info.one(w, NS.ikind.v(b, NS.Rg{a, z}, J(len, t, a, z), B.Tags.find(tags, TXR(len, t, a, J(len, t, a, z)))), nalt, i), m0,
    G.GSTR(ISNb(b, B.Tags.find(tags, TXR(len, t, a, J(len, t, a, z))), TXR(len, t, a, J(len, t, a, z)), TXR(len, t, a, z), nalt, i)),
    G.GOK(ISNb(b, B.Tags.find(tags, TXR(len, t, a, J(len, t, a, z))), TXR(len, t, a, J(len, t, a, z)), TXR(len, t, a, z), nalt, i))):
  match b:
    case True{}:
      info.pa(B.Num.per_allele(B.Tags.find(tags, TXR(len, t, a, J(len, t, a, z)))), len, t, d, hl, nalt, i, a, z, hpz, w, m0, r)
    case False{}:
      +haz = W.pv_a(len, a, z, hpz)
      +hzl = W.pv_z(len, a, z, hpz)
      +hjz = SC.lt_of(J(len, t, a, z), z, SC.j_hi(len, t, d, a, z, 61, hl, haz, hzl, {==}),
        Equal.trans(Bool, U32.is_eq(J(len, t, a, z), z), U32.is_eq(z, J(len, t, a, z)), False{}, U32EQ(J(len, t, a, z), z), hb))
      info.m(B.Tags.find(tags, TXR(len, t, a, J(len, t, a, z))), len, t, d, hl, nalt, i, a, z, hpz, hjz, w, m0, r)

# One INFO entry a .. z-1 (of its kind) in the record for ALT i of nalt:
# what B.Info.split.num gives.
def info_one_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +nalt: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.info.one(w, KD.IKIND(len, t, tags, NS.Rg{a, z}), nalt, i), m0, G.GSTR(ISN(tags, nalt, i, TXR(len, t, a, z))), G.GOK(ISN(tags, nalt, i, TXR(len, t, a, z)))):
  +KY = TXR(len, t, a, J(len, t, a, z))
  +M = B.Tags.find(tags, KY)
  +bb = U32.is_eq(z, J(len, t, a, z))
  %Equal.sym(B.Got, ISN(tags, nalt, i, TXR(len, t, a, z)), ISNb(bb, M, KY, TXR(len, t, a, z), nalt, i), isn_eq(len, t, d, tags, nalt, i, a, z, hl, W.pv_a(len, a, z, hpz), W.pv_z(len, a, z, hpz))) :
    S.WS(len, t, NS.info.one(w, KD.IKIND(len, t, tags, NS.Rg{a, z}), nalt, i), m0, G.GSTR(_), G.GOK(_))
  info.b(bb, len, t, d, hl, tags, nalt, i, a, z, hpz, {==}, w, m0, r)

# ---------------------------------------------------------------------------
# INFO: all entries, separated by ';' (B.Info.split)
# ---------------------------------------------------------------------------

def Rgs() -> Data:
  List<&2, NS.Rg>

def ISNS(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +nalt: Nat, +i: Nat, xs: Rgs()) -> G.Gs():
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      Con{ISN(tags, nalt, i, WT.TX(len, t, x)), ISNS(len, t, tags, nalt, i, r)}

def seps_ps(+first: Bool, +c: U32) -> {WT.SEPS(first, c) == G.PS(first, NR.chars([c])) : String}:
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

law info_go_t:
  for +xs: Rgs()
  for +first: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +tags: Tags()
  for +nalt: Nat
  for +i: Nat
  for +hps: {K.ALLPV(len, xs) == True{} : Bool}
  for -w: NS.Sw
  for +m0: W.Wm
  for r: W.Rel(len, t, w, m0)
  S.WS(len, t, NS.info.go(KD.MAPI(len, t, tags, xs), w, nalt, i, first), m0, G.JT(ISNS(len, t, tags, nalt, i, xs), first, ";"), G.JG(ISNS(len, t, tags, nalt, i, xs)))

def info_go_t(xs, first, len, t, d, hl, tags, nalt, i, hps, w, m0, r):
  match xs:
    case Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Con{NS.Rg{+a, +z}, +rr}:
      +x = {NS.Rg{a, z} : NS.Rg}
      +hpx = N.and_true_l(W.PV(len, x), K.ALLPV(len, rr), hps)
      +hpr = N.and_true_r(W.PV(len, x), K.ALLPV(len, rr), hps)
      +g = ISN(tags, nalt, i, WT.TX(len, t, x))
      +R = ISNS(len, t, tags, nalt, i, rr)
      -sw = NS.sep(w, first, 59)
      S.ws_eq(len, t, NS.info.go(KD.MAPI(len, t, tags, rr), NS.info.one(sw, KD.IKIND(len, t, tags, x), nalt, i), nalt, i, False{}), m0,
        String.append(WT.SEPS(first, 59), String.append(G.GSTR(g), G.JT(R, False{}, ";"))), G.JT(Con{g, R}, first, ";"),
        Bool.and(True{}, Bool.and(G.GOK(g), G.JG(R))), G.JG(Con{g, R}),
        %Equal.sym(String, WT.SEPS(first, 59), G.PS(first, NR.chars([59])), seps_ps(first, 59)) : {String.append(_, String.append(G.GSTR(g), G.JT(R, False{}, ";"))) == G.JT(Con{g, R}, first, ";") : String}; {==},
        {==},
        S.ws_seq(len, t, sw, v => NS.info.go(KD.MAPI(len, t, tags, rr), NS.info.one(v, KD.IKIND(len, t, tags, x), nalt, i), nalt, i, False{}), m0,
          WT.SEPS(first, 59), String.append(G.GSTR(g), G.JT(R, False{}, ";")), True{}, Bool.and(G.GOK(g), G.JG(R)),
          S.ws_sep(len, t, d, hl, first, 59, {==}, w, m0, r),
          +m1 => r1 => S.ws_seq(len, t, NS.info.one(sw, KD.IKIND(len, t, tags, x), nalt, i), v => NS.info.go(KD.MAPI(len, t, tags, rr), v, nalt, i, False{}), m1,
            G.GSTR(g), G.JT(R, False{}, ";"), G.GOK(g), G.JG(R),
            info_one_t(len, t, d, hl, tags, nalt, i, a, z, hpx, sw, m1, r1),
            +m2 => r2 => info_go_t(rr, False{}, len, t, d, hl, tags, nalt, i, hpr, NS.info.one(sw, KD.IKIND(len, t, tags, x), nalt, i), m2, r2))))

law isg:
  for +xs: Rgs()
  for +len: U32
  for +t: AT.Tree<U32>
  for +tags: Tags()
  for +nalt: Nat
  for +i: Nat
  {B.Info.split.go(K.TXS(len, t, xs), tags, nalt, i) == ISNS(len, t, tags, nalt, i, xs) : G.Gs()}

def isg(xs, len, t, tags, nalt, i):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(G.Gs(), B.Info.split.go(K.TXS(len, t, r), tags, nalt, i), ISNS(len, t, tags, nalt, i, r), isg(r, len, t, tags, nalt, i)) :
        {Con{ISN(tags, nalt, i, WT.TX(len, t, x)), _} == ISNS(len, t, tags, nalt, i, Con{x, r}) : G.Gs()}
      {==}

def INFOS(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +nalt: Nat, +i: Nat, +a: U32, +z: U32) -> B.Got:
  B.Info.split(TXR(len, t, a, z), tags, nalt, i)

def info.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +nalt: Nat, +i: Nat,
  +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +hg: {G.JG(ISNS(len, t, tags, nalt, i, K.CUT(len, t, a, z, 59))) == True{} : Bool}) ->
  ({G.GOK(INFOS(len, t, tags, nalt, i, a, z)) == True{} : Bool} & {G.JT(ISNS(len, t, tags, nalt, i, K.CUT(len, t, a, z, 59)), True{}, ";") == G.GSTR(INFOS(len, t, tags, nalt, i, a, z)) : String}):
  +XS = K.CUT(len, t, a, z, 59)
  +L = ISNS(len, t, tags, nalt, i, XS)
  +eI = {%K.cut_tx(len, t, d, a, z, 59, hl, haz, hz, {==}) :
      {B.Got.join(B.Info.split.go(_, tags, nalt, i), ";") == B.Got{G.JT(L, True{}, ";")} : B.Got};
    %Equal.sym(G.Gs(), B.Info.split.go(K.TXS(len, t, XS), tags, nalt, i), L, isg(XS, len, t, tags, nalt, i)) :
      {B.Got.join(_, ";") == B.Got{G.JT(L, True{}, ";")} : B.Got};
    G.join_t(L, ";", hg) : {INFOS(len, t, tags, nalt, i, a, z) == B.Got{G.JT(L, True{}, ";")} : B.Got}}
  ({%Equal.sym(B.Got, INFOS(len, t, tags, nalt, i, a, z), B.Got{G.JT(L, True{}, ";")}, eI) : {G.GOK(_) == True{} : Bool}; {==} : {G.GOK(INFOS(len, t, tags, nalt, i, a, z)) == True{} : Bool}},
   {%Equal.sym(B.Got, INFOS(len, t, tags, nalt, i, a, z), B.Got{G.JT(L, True{}, ";")}, eI) : {G.JT(L, True{}, ";") == G.GSTR(_) : String}; {==} : {G.JT(L, True{}, ";") == G.GSTR(INFOS(len, t, tags, nalt, i, a, z)) : String}})

# INFO a .. z-1 in the record for ALT i of nalt: what B.Info.split gives.
def info_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +nalt: Nat, +i: Nat,
  +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.info.go(KD.MAPI(len, t, tags, K.CUT(len, t, a, z, 59)), w, nalt, i, True{}), m0,
    G.GSTR(INFOS(len, t, tags, nalt, i, a, z)), G.GOK(INFOS(len, t, tags, nalt, i, a, z))):
  +XS = K.CUT(len, t, a, z, 59)
  S.ws_imp(len, t, NS.info.go(KD.MAPI(len, t, tags, XS), w, nalt, i, True{}), m0,
    G.JT(ISNS(len, t, tags, nalt, i, XS), True{}, ";"), G.JG(ISNS(len, t, tags, nalt, i, XS)),
    G.GSTR(INFOS(len, t, tags, nalt, i, a, z)), G.GOK(INFOS(len, t, tags, nalt, i, a, z)),
    hg => info.k(len, t, d, hl, tags, nalt, i, a, z, haz, hz, hg),
    info_go_t(XS, True{}, len, t, d, hl, tags, nalt, i, K.cut_pv(len, t, d, a, z, 59, hl, haz, hz, {==}), w, m0, r))
