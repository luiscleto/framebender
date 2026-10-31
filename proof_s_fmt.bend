import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_ws.bend as S
import ./proof_s_cut.bend as K
import ./proof_s_scan.bend as SC
import ./proof_s_read.bend as RD
import ./proof_s_vals.bend as VL
import ./proof_s_gtspec.bend as G
import ./proof_s_gt.bend as GT
import ./proof_s_kinds.bend as KD
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A sample's column in the record for ALT i (norm_split.bend's copies,
# fmt.one, fmt.go, sample) writes what B.Fmt.split gives; the column's values
# are found in place (K.SP, cut at ':'). Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def Ss() -> Data:
  List<&2, String>

def Rgs() -> Data:
  List<&2, NS.Rg>

def Tags() -> Data:
  List<&2, B.Tag>

# ---------------------------------------------------------------------------
# Separators of a genotype: the '/' and the '|'
# ---------------------------------------------------------------------------

def sc.k(+e1: Bool, +e2: Bool, +x: U32, +r: L32(), +he1: {U32.is_eq(x, 47) == e1 : Bool}, +he2: {U32.is_eq(x, 124) == e2 : Bool},
  +ih: {B.Gt.seps(NR.chars(r)) == Nat.add(FD.count(r, 47), FD.count(r, 124)) : Nat}) ->
  {Nat.add(Bool.pick(Nat, Bool.or(e1, e2), 1n, 0n), B.Gt.seps(NR.chars(r))) == Nat.add(FD.count.if(e1, FD.count(r, 47)), FD.count.if(e2, FD.count(r, 124))) : Nat}:
  match e1 e2:
    case True{} True{}:
      +ex = U.is_eq_true(x, 47, he1)
      Empty.absurd({Nat.add(1n, B.Gt.seps(NR.chars(r))) == Nat.add(Nat.add(1n, FD.count(r, 47)), Nat.add(1n, FD.count(r, 124))) : Nat},
        P.false_ne_true(%ex : {U32.is_eq(_, 124) == True{} : Bool}; he2))
    case True{} False{}:
      %Equal.sym(Nat, B.Gt.seps(NR.chars(r)), Nat.add(FD.count(r, 47), FD.count(r, 124)), ih) : {Nat.add(1n, _) == Nat.add(Nat.add(1n, FD.count(r, 47)), FD.count(r, 124)) : Nat}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, B.Gt.seps(NR.chars(r)), Nat.add(FD.count(r, 47), FD.count(r, 124)), ih) : {Nat.add(1n, _) == Nat.add(FD.count(r, 47), Nat.add(1n, FD.count(r, 124))) : Nat}
      %Equal.sym(Nat, Nat.add(FD.count(r, 47), Nat.add(1n, FD.count(r, 124))), 1n+Nat.add(FD.count(r, 47), FD.count(r, 124)), N.add_succ(FD.count(r, 47), FD.count(r, 124))) :
        {Nat.add(1n, Nat.add(FD.count(r, 47), FD.count(r, 124))) == _ : Nat}
      {==}
    case False{} False{}:
      ih

law seps_count:
  for +xs: L32()
  {B.Gt.seps(NR.chars(xs)) == Nat.add(FD.count(xs, 47), FD.count(xs, 124)) : Nat}

def seps_count(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      sc.k(U32.is_eq(x, 47), U32.is_eq(x, 124), x, r, {==}, {==}, seps_count(r))

# ---------------------------------------------------------------------------
# copies: the sample's copies (B.Gt.copies of B.Fmt.gt)
# ---------------------------------------------------------------------------

def BT(+len: U32, +t: AT.Tree<U32>) -> D.Bytes:
  C.BT(len, t)

def is_kgt(+f: NS.Fk) -> Bool:
  match f:
    case NS.KGt{}:
      True{}
    case _:
      False{}

def kgt_num(+M: Maybe<&2, B.Num>) -> {is_kgt(NS.fkind.num(M)) == False{} : Bool}:
  match M:
    case None{}:
      {==}
    case Some{B.NumA{}}:
      {==}
    case Some{B.NumR{}}:
      {==}
    case Some{B.NumG{}}:
      {==}
    case Some{B.NumOther{}}:
      {==}
    case Some{B.NumUnknown{}}:
      {==}

def MN2() -> Data:
  Maybe<&2, Nat>

def cp.n(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +k1: Nat,
  +ek1: {Nat.add(k1, 1n) == Nat.add(0n, SC.NP(len, t, a, z, 47)) : Nat},
  c2: SC.CNT(len, t, 0n, a, z, 124, NS.count(C.BT(len, t), NS.Rg{a, z}, 124)), +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}) ->
  {NS.copies.n(k1, NS.count(C.BT(len, t), NS.Rg{a, z}, 124)) == (C.BT(len, t), Some{1n+B.Gt.seps(WT.TX(len, t, NS.Rg{a, z}))}) : D.Bytes & MN2()}:
  (+k2, e) = c2
  (eq2, ek2) = e
  +xs = SC.BS(len, t, a, z)
  %Equal.sym(D.Bytes & Nat, NS.count(C.BT(len, t), NS.Rg{a, z}, 124), (C.BT(len, t), k2), eq2) :
    {NS.copies.n(k1, _) == (C.BT(len, t), Some{1n+B.Gt.seps(WT.TX(len, t, NS.Rg{a, z}))}) : D.Bytes & MN2()}
  %Equal.sym(String, WT.TX(len, t, NS.Rg{a, z}), NR.chars(xs), RD.tx_eq(len, t, a, z, haz)) :
    {(C.BT(len, t), Some{1n+Nat.add(k1, k2)}) == (C.BT(len, t), Some{1n+B.Gt.seps(_)}) : D.Bytes & MN2()}
  %Equal.sym(Nat, B.Gt.seps(NR.chars(xs)), Nat.add(FD.count(xs, 47), FD.count(xs, 124)), seps_count(xs)) :
    {(C.BT(len, t), Some{1n+Nat.add(k1, k2)}) == (C.BT(len, t), Some{1n+_}) : D.Bytes & MN2()}
  %Equal.sym(Nat, k1, FD.count(xs, 47), SC.cnt_val(len, t, a, z, 47, k1, ek1)) : {(C.BT(len, t), Some{1n+Nat.add(_, k2)}) == (C.BT(len, t), Some{1n+Nat.add(FD.count(xs, 47), FD.count(xs, 124))}) : D.Bytes & MN2()}
  %Equal.sym(Nat, k2, FD.count(xs, 124), SC.cnt_val(len, t, a, z, 124, k2, ek2)) : {(C.BT(len, t), Some{1n+Nat.add(FD.count(xs, 47), _)}) == (C.BT(len, t), Some{1n+Nat.add(FD.count(xs, 47), FD.count(xs, 124))}) : D.Bytes & MN2()}
  {==}

def cp.c(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  c1: SC.CNT(len, t, 0n, a, z, 47, NS.count(C.BT(len, t), NS.Rg{a, z}, 47))) ->
  {NS.copies.c(NS.count(C.BT(len, t), NS.Rg{a, z}, 47), NS.Rg{a, z}) == (C.BT(len, t), Some{1n+B.Gt.seps(WT.TX(len, t, NS.Rg{a, z}))}) : D.Bytes & MN2()}:
  (+k1, e) = c1
  (eq1, ek1) = e
  %Equal.sym(D.Bytes & Nat, NS.count(C.BT(len, t), NS.Rg{a, z}, 47), (C.BT(len, t), k1), eq1) :
    {NS.copies.c(_, NS.Rg{a, z}) == (C.BT(len, t), Some{1n+B.Gt.seps(WT.TX(len, t, NS.Rg{a, z}))}) : D.Bytes & MN2()}
  cp.n(len, t, a, z, k1, ek1, SC.count_t(len, t, d, a, z, 124, hl, haz, hzl, {==}), haz)

def cp.d(+dot: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  {NS.copies.dot(dot, C.BT(len, t), NS.Rg{a, z}) == (C.BT(len, t), Bool.pick(MN2(), dot, None{}, Some{1n+B.Gt.seps(WT.TX(len, t, NS.Rg{a, z}))})) : D.Bytes & MN2()}:
  match dot:
    case True{}:
      {==}
    case False{}:
      cp.c(len, t, d, hl, a, z, W.pv_a(len, a, z, hp), W.pv_z(len, a, z, hp), SC.count_t(len, t, d, a, z, 47, hl, W.pv_a(len, a, z, hp), W.pv_z(len, a, z, hp), {==}))

# The GT value v: its copies.
def cp.v(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  {NS.copies.v(NS.is1(C.BT(len, t), NS.Rg{a, z}, 46), NS.Rg{a, z}) == (C.BT(len, t), B.Gt.copies(Some{WT.TX(len, t, NS.Rg{a, z})})) : D.Bytes & MN2()}:
  +x = {NS.Rg{a, z} : NS.Rg}
  %Equal.sym(D.Bytes & Bool, NS.is1(C.BT(len, t), x, 46), (C.BT(len, t), RD.IS1(len, t, x, 46)), RD.is1_t(len, t, x, 46)) :
    {NS.copies.v(_, x) == (C.BT(len, t), B.Gt.copies(Some{WT.TX(len, t, x)})) : D.Bytes & MN2()}
  %RD.is1_v(len, t, d, x, 46, hl, hp) :
    {NS.copies.dot(RD.IS1(len, t, x, 46), C.BT(len, t), x) == (C.BT(len, t), Bool.pick(MN2(), _, None{}, Some{1n+B.Gt.seps(WT.TX(len, t, x))})) : D.Bytes & MN2()}
  cp.d(RD.IS1(len, t, x, 46), len, t, d, hl, a, z, hp)

def GTO(ks: Ss(), vs: Ss()) -> MN2():
  B.Gt.copies(B.Fmt.gt(ks, vs))

# ---------------------------------------------------------------------------
# A column's values, found in place
# ---------------------------------------------------------------------------

def LL() -> Data:
  List<&2, List<&2, U32>>

# The end of the value at s: the first ':' from s, or z.
def J(+len: U32, +t: AT.Tree<U32>, +s: U32, +z: U32) -> U32:
  SC.J(len, t, s, z, 58)

# The texts of the values from s on (String.split of s .. z-1 at ':').
def VT(+len: U32, +t: AT.Tree<U32>, +s: U32, +z: U32) -> Ss():
  K.CHS(K.SP(len, t, s, z, 58))

# Those after the first.
def VR(+len: U32, +t: AT.Tree<U32>, +s: U32, +z: U32) -> Ss():
  K.CHS(SC.TS(len, t, J(len, t, s, z), z, 58))

def vt_first(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {VT(len, t, s, z) == Con{WT.TX(len, t, NS.Rg{s, J(len, t, s, z)}), VR(len, t, s, z)} : Ss()}:
  +j = J(len, t, s, z)
  %Equal.sym(LL(), K.SP(len, t, s, z, 58), Con{SC.BS(len, t, s, j), SC.TS(len, t, j, z, 58)}, SC.sp_first(len, t, d, s, z, 58, hl, hsz, hz, {==})) :
    {K.CHS(_) == Con{WT.TX(len, t, NS.Rg{s, j}), VR(len, t, s, z)} : Ss()}
  %Equal.sym(String, WT.TX(len, t, NS.Rg{s, j}), NR.chars(SC.BS(len, t, s, j)), RD.tx_eq(len, t, s, j, SC.j_lo(len, t, d, s, z, 58, hl, hsz, hz, {==}))) :
    {Con{NR.chars(SC.BS(len, t, s, j)), VR(len, t, s, z)} == Con{_, VR(len, t, s, z)} : Ss()}
  {==}

# Not the last value: those after it start at J + 1.
def vr_next(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(J(len, t, s, z)), n(z)) == True{} : Bool}) ->
  {VR(len, t, s, z) == VT(len, t, (J(len, t, s, z) + 1 : U32), z) : Ss()}:
  +j = J(len, t, s, z)
  %Equal.sym(LL(), SC.TS(len, t, j, z, 58), K.SP(len, t, (j + 1 : U32), z, 58),
    SC.ts_next(len, t, d, j, z, 58, hl, hz, hlt, SC.j_hit(len, t, d, s, z, 58, hl, hsz, hz, {==}, hlt))) :
    {K.CHS(_) == VT(len, t, (j + 1 : U32), z) : Ss()}
  {==}

# The last value: none after it.
def vr_last(+len: U32, +t: AT.Tree<U32>, +s: U32, +z: U32, +he: {U32.is_eq(J(len, t, s, z), z) == True{} : Bool}) ->
  {VR(len, t, s, z) == Nil{} : Ss()}:
  +j = J(len, t, s, z)
  %Equal.sym(LL(), SC.TS(len, t, j, z, 58), Nil{}, SC.ts_last(len, t, j, z, 58, SC.u_eq(j, z, he))) :
    {K.CHS(_) == Nil{} : Ss()}
  {==}

# The value at s is within the line.
def pv_j(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {W.PV(len, NS.Rg{s, J(len, t, s, z)}) == True{} : Bool}:
  +j = J(len, t, s, z)
  W.pv_mk(len, s, j, SC.j_lo(len, t, d, s, z, 58, hl, hsz, hz, {==}),
    N.le_trans(n(j), n(z), n(len), SC.j_hi(len, t, d, s, z, 58, hl, hsz, hz, {==}), hz))

# ---------------------------------------------------------------------------
# copies: the sample's copies, found in place
# ---------------------------------------------------------------------------

def BTJ(+len: U32, +t: AT.Tree<U32>, +j: U32) -> D.Bytes & U32:
  (C.BT(len, t), j)

def cps_skip(+len: U32, +t: AT.Tree<U32>, +f: NS.Fk, +fs: List<&2, NS.Fk>, +j: U32, +s: U32, +z: U32, +hf: {is_kgt(f) == False{} : Bool}) ->
  {NS.copies(Con{f, fs}, False{}, NS.hgt(Con{f, fs}), (C.BT(len, t), j), s, z) ==
    NS.copies(fs, U32.is_eq(j, z), NS.hgt(fs), F.find(C.BT(len, t), (j + 1 : U32), z, 58), (j + 1 : U32), z) : D.Bytes & MN2()}:
  match f:
    case NS.KGt{}:
      Empty.absurd({NS.copies(Con{NS.KGt{}, fs}, False{}, True{}, (C.BT(len, t), j), s, z) ==
        NS.copies(fs, U32.is_eq(j, z), NS.hgt(fs), F.find(C.BT(len, t), (j + 1 : U32), z, 58), (j + 1 : U32), z) : D.Bytes & MN2()},
        P.false_ne_true(Equal.sym(Bool, True{}, False{}, hf)))
    case NS.KKeep{}:
      {==}
    case NS.KVal{+num}:
      {==}
    case NS.KBad{}:
      {==}

# No values left: two copies (B.Fmt.gt finds no GT value).
def cps_done(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +kt: Ss(), +j: U32, +s: U32, +z: U32) ->
  {NS.copies(KD.MAPF(tags, kt), True{}, NS.hgt(KD.MAPF(tags, kt)), (C.BT(len, t), j), s, z) == (C.BT(len, t), GTO(kt, Nil{})) : D.Bytes & MN2()}:
  match kt:
    case Nil{}:
      {==}
    case Con{+k, +r}:
      {==}

def cps.e(+e: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +kt: Ss(), +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +he: {U32.is_eq(J(len, t, s, z), z) == e : Bool},
  ih: @+s2: U32 -> @+h2: {Nat.is_le(n(s2), n(z)) == True{} : Bool} ->
    {NS.copies(KD.MAPF(tags, kt), False{}, NS.hgt(KD.MAPF(tags, kt)), (C.BT(len, t), J(len, t, s2, z)), s2, z) == (C.BT(len, t), GTO(kt, VT(len, t, s2, z))) : D.Bytes & MN2()}) ->
  {NS.copies(KD.MAPF(tags, kt), e, NS.hgt(KD.MAPF(tags, kt)), (C.BT(len, t), J(len, t, (J(len, t, s, z) + 1 : U32), z)), (J(len, t, s, z) + 1 : U32), z) ==
    (C.BT(len, t), GTO(kt, VR(len, t, s, z))) : D.Bytes & MN2()}:
  match e:
    case True{}:
      +j = J(len, t, s, z)
      %Equal.sym(Ss(), VR(len, t, s, z), Nil{}, vr_last(len, t, s, z, he)) : {NS.copies(KD.MAPF(tags, kt), True{}, NS.hgt(KD.MAPF(tags, kt)), (C.BT(len, t), J(len, t, (j + 1 : U32), z)), (j + 1 : U32), z) == (C.BT(len, t), GTO(kt, _)) : D.Bytes & MN2()}
      cps_done(len, t, tags, kt, J(len, t, (j + 1 : U32), z), (j + 1 : U32), z)
    case False{}:
      +j = J(len, t, s, z)
      +hlt = SC.lt_of(j, z, SC.j_hi(len, t, d, s, z, 58, hl, hsz, hz, {==}), he)
      %Equal.sym(Ss(), VR(len, t, s, z), VT(len, t, (j + 1 : U32), z), vr_next(len, t, d, hl, s, z, hsz, hz, hlt)) :
        {NS.copies(KD.MAPF(tags, kt), False{}, NS.hgt(KD.MAPF(tags, kt)), (C.BT(len, t), J(len, t, (j + 1 : U32), z)), (j + 1 : U32), z) == (C.BT(len, t), GTO(kt, _)) : D.Bytes & MN2()}
      ih((j + 1 : U32), SC.j1_le(len, t, d, j, z, hl, hz, hlt))

def cps.g(+g: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +k: String, +kt: Ss(), +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  ih: @+s2: U32 -> @+h2: {Nat.is_le(n(s2), n(z)) == True{} : Bool} ->
    {NS.copies(KD.MAPF(tags, kt), False{}, NS.hgt(KD.MAPF(tags, kt)), (C.BT(len, t), J(len, t, s2, z)), s2, z) == (C.BT(len, t), GTO(kt, VT(len, t, s2, z))) : D.Bytes & MN2()}) ->
  {NS.copies(Con{Bool.pick(NS.Fk, g, NS.KGt{}, NS.fkind.num(B.Tags.find(tags, k))), KD.MAPF(tags, kt)}, False{},
      NS.hgt(Con{Bool.pick(NS.Fk, g, NS.KGt{}, NS.fkind.num(B.Tags.find(tags, k))), KD.MAPF(tags, kt)}), (C.BT(len, t), J(len, t, s, z)), s, z) ==
    (C.BT(len, t), B.Gt.copies(B.Fmt.gt.put(g, WT.TX(len, t, NS.Rg{s, J(len, t, s, z)}), B.Fmt.gt(kt, VR(len, t, s, z))))) : D.Bytes & MN2()}:
  match g:
    case True{}:
      +j = J(len, t, s, z)
      cp.v(len, t, d, hl, s, j, pv_j(len, t, d, hl, s, z, hsz, hz))
    case False{}:
      +j = J(len, t, s, z)
      +f = NS.fkind.num(B.Tags.find(tags, k))
      +KT = KD.MAPF(tags, kt)
      %Equal.sym(D.Bytes & MN2(), NS.copies(Con{f, KT}, False{}, NS.hgt(Con{f, KT}), (C.BT(len, t), j), s, z),
        NS.copies(KT, U32.is_eq(j, z), NS.hgt(KT), F.find(C.BT(len, t), (j + 1 : U32), z, 58), (j + 1 : U32), z),
        cps_skip(len, t, f, KT, j, s, z, kgt_num(B.Tags.find(tags, k)))) :
        {_ == (C.BT(len, t), GTO(kt, VR(len, t, s, z))) : D.Bytes & MN2()}
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), (j + 1 : U32), z, 58), (C.BT(len, t), J(len, t, (j + 1 : U32), z)), SC.find_step(len, t, (j + 1 : U32), z, 58)) :
        {NS.copies(KT, U32.is_eq(j, z), NS.hgt(KT), _, (j + 1 : U32), z) == (C.BT(len, t), GTO(kt, VR(len, t, s, z))) : D.Bytes & MN2()}
      cps.e(U32.is_eq(j, z), len, t, d, hl, tags, kt, s, z, hsz, hz, {==}, ih)

law cps_t:
  for +kss: Ss()
  for +s: U32
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +tags: Tags()
  for +z: U32
  for +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}
  for +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool}
  {NS.copies(KD.MAPF(tags, kss), False{}, NS.hgt(KD.MAPF(tags, kss)), (C.BT(len, t), J(len, t, s, z)), s, z) == (C.BT(len, t), GTO(kss, VT(len, t, s, z))) : D.Bytes & MN2()}

def cps_t(kss, s, len, t, d, hl, tags, z, hsz, hz):
  match kss:
    case Nil{}:
      %Equal.sym(Ss(), VT(len, t, s, z), Con{WT.TX(len, t, NS.Rg{s, J(len, t, s, z)}), VR(len, t, s, z)}, vt_first(len, t, d, hl, s, z, hsz, hz)) :
        {NS.copies(Nil{}, False{}, False{}, (C.BT(len, t), J(len, t, s, z)), s, z) == (C.BT(len, t), GTO(Nil{}, _)) : D.Bytes & MN2()}
      {==}
    case Con{+k, +kt}:
      %Equal.sym(Ss(), VT(len, t, s, z), Con{WT.TX(len, t, NS.Rg{s, J(len, t, s, z)}), VR(len, t, s, z)}, vt_first(len, t, d, hl, s, z, hsz, hz)) :
        {NS.copies(KD.MAPF(tags, Con{k, kt}), False{}, NS.hgt(KD.MAPF(tags, Con{k, kt})), (C.BT(len, t), J(len, t, s, z)), s, z) == (C.BT(len, t), GTO(Con{k, kt}, _)) : D.Bytes & MN2()}
      cps.g(String.eq(k, "GT"), len, t, d, hl, tags, k, kt, s, z, hsz, hz, +s2 => +h2 => cps_t(kt, s2, len, t, d, hl, tags, z, h2, hz))

# ---------------------------------------------------------------------------
# fmt.one: one value of a sample (B.Fmt.split.one)
# ---------------------------------------------------------------------------

def got_of(+m: Maybe<&2, String>, +c: B.Code) -> ({G.GSTR(B.Got.of(m, c)) == VL.STR(m) : String} & {G.GOK(B.Got.of(m, c)) == VL.ISS(m) : Bool}):
  match m:
    case Some{+s}:
      ({==}, {==})
    case None{}:
      ({==}, {==})

def go1(+m: Maybe<&2, String>, +c: B.Code) -> {VL.STR(m) == G.GSTR(B.Got.of(m, c)) : String}:
  match m:
    case Some{+s}:
      {==}
    case None{}:
      {==}

def go2(+m: Maybe<&2, String>, +c: B.Code) -> {VL.ISS(m) == G.GOK(B.Got.of(m, c)) : Bool}:
  match m:
    case Some{+s}:
      {==}
    case None{}:
      {==}

def FSO(+k: String, +v: String, +tags: Tags(), +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat) -> B.Got:
  B.Fmt.split.one(k, v, tags, o, nalt, cp, i)

def fo.val(+num: B.Num, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +a: U32, +z: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.vals(w, num, nalt, cp, i, NS.Rg{a, z}), m0,
    G.GSTR(B.Got.of(B.Vals.split(num, nalt, cp, i, WT.TX(len, t, NS.Rg{a, z})), B.BadCount{})), G.GOK(B.Got.of(B.Vals.split(num, nalt, cp, i, WT.TX(len, t, NS.Rg{a, z})), B.BadCount{}))):
  +V0 = B.Vals.split(num, nalt, cp, i, WT.TX(len, t, NS.Rg{a, z}))
  S.ws_eq(len, t, NS.vals(w, num, nalt, cp, i, NS.Rg{a, z}), m0, VL.STR(V0), G.GSTR(B.Got.of(V0, B.BadCount{})), VL.ISS(V0), G.GOK(B.Got.of(V0, B.BadCount{})),
    go1(V0, B.BadCount{}), go2(V0, B.BadCount{}),
    VL.vals_t(len, t, d, hl, a, z, hp, num, nalt, cp, i, w, m0, r))

def fo.m(+M: Maybe<&2, B.Num>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +k: String, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +a: U32, +z: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +o: Bool, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.fmt.one(w, NS.fkind.num(M), o, nalt, cp, i, NS.Rg{a, z}), m0,
    G.GSTR(B.Fmt.split.num(M, k, WT.TX(len, t, NS.Rg{a, z}), nalt, cp, i)), G.GOK(B.Fmt.split.num(M, k, WT.TX(len, t, NS.Rg{a, z}), nalt, cp, i))):
  match M:
    case None{}:
      S.ws_fail(len, t, "", False{}, w, m0, r)
    case Some{B.NumUnknown{}}:
      S.ws_fail(len, t, "", False{}, w, m0, r)
    case Some{B.NumOther{}}:
      S.ws_cpr(len, t, d, hl, NS.Rg{a, z}, hp, w, m0, r)
    case Some{B.NumA{}}:
      fo.val(B.NumA{}, len, t, d, hl, nalt, cp, i, a, z, hp, w, m0, r)
    case Some{B.NumR{}}:
      fo.val(B.NumR{}, len, t, d, hl, nalt, cp, i, a, z, hp, w, m0, r)
    case Some{B.NumG{}}:
      fo.val(B.NumG{}, len, t, d, hl, nalt, cp, i, a, z, hp, w, m0, r)

def fo.g(+g: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +k: String, +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +a: U32, +z: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.fmt.one(w, Bool.pick(NS.Fk, g, NS.KGt{}, NS.fkind.num(B.Tags.find(tags, k))), o, nalt, cp, i, NS.Rg{a, z}), m0,
    G.GSTR(Bool.pick(B.Got, g, B.Gt.split(o, nalt, i, WT.TX(len, t, NS.Rg{a, z})), B.Fmt.split.num(B.Tags.find(tags, k), k, WT.TX(len, t, NS.Rg{a, z}), nalt, cp, i))),
    G.GOK(Bool.pick(B.Got, g, B.Gt.split(o, nalt, i, WT.TX(len, t, NS.Rg{a, z})), B.Fmt.split.num(B.Tags.find(tags, k), k, WT.TX(len, t, NS.Rg{a, z}), nalt, cp, i)))):
  match g:
    case True{}:
      GT.gt_t(len, t, d, hl, o, nalt, i, a, z, hp, bd, hbd, w, m0, r)
    case False{}:
      fo.m(B.Tags.find(tags, k), len, t, d, hl, k, nalt, cp, i, a, z, hp, o, w, m0, r)

# One value v of a sample, under the FORMAT key k: what B.Fmt.split.one gives.
def fmt_one_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +k: String, +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +a: U32, +z: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.fmt.one(w, KD.FKIND(tags, k), o, nalt, cp, i, NS.Rg{a, z}), m0,
    G.GSTR(FSO(k, WT.TX(len, t, NS.Rg{a, z}), tags, o, nalt, cp, i)), G.GOK(FSO(k, WT.TX(len, t, NS.Rg{a, z}), tags, o, nalt, cp, i))):
  fo.g(String.eq(k, "GT"), len, t, d, hl, tags, k, o, nalt, cp, i, a, z, hp, bd, hbd, w, m0, r)

# ---------------------------------------------------------------------------
# fmt.go and sample: a sample's column (B.Fmt.split)
# ---------------------------------------------------------------------------

def FSV(+tags: Tags(), +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, kss: Ss(), vs: Ss()) -> G.Gs():
  B.Fmt.split.go(kss, vs, tags, o, nalt, cp, i)

def seps_ps(+first: Bool, +c: U32) -> {WT.SEPS(first, c) == G.PS(first, NR.chars([c])) : String}:
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

def fw_eq(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +s: U32, +z: U32) ->
  {NS.fone.w(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, s, z) == (NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, J(len, t, s, z)) : NS.Sw & U32}:
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s, z, 58), (C.BT(len, t), J(len, t, s, z)), SC.find_step(len, t, s, z, 58)) :
    {NS.fone.f(_, C.BT(l2, t2), p, ok) == (NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, J(len, t, s, z)) : NS.Sw & U32}
  {==}

# A writer state's fone.w: the state, with the end of the value at s (and
# the state's Rel, handed back).
def fone_w(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m: W.Wm, r: W.Rel(len, t, w, m), +s: U32, +z: U32) ->
  ({NS.fone.w(w, s, z) == (w, J(len, t, s, z)) : NS.Sw & U32} & W.Rel(len, t, w, m)):
  match m:
    case W.Wm{+out, +p, +ok}:
      (+l2, q) = r
      (+t2, e) = q
      (eq, r1) = e
      (hok, r2) = r1
      (hv, hp) = r2
      %Equal.sym(NS.Sw, w, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, eq) :
        ({NS.fone.w(_, s, z) == (_, J(len, t, s, z)) : NS.Sw & U32} & W.Rel(len, t, _, W.Wm{out, p, ok}))
      (fw_eq(len, t, l2, t2, p, ok, s, z), (l2, (t2, ({==}, (hok, (hv, hp))))))

# No values left: nothing more written.
def fgo_done(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +kt: Ss(), +j: U32, +s: U32, +z: U32,
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), True{}, (w, j), s, z, o, nalt, cp, i, False{}), m0,
    G.JT(FSV(tags, o, nalt, cp, i, kt, Nil{}), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, Nil{}))):
  match kt:
    case Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Con{+k, +r2}:
      S.ws_ret(len, t, w, m0, r)

# The bound 2^32 (GT.gt_t's), wrapped: the checker's error printer never
# meets Nat.pow(2n, 32n) in the context of the defs that carry it.
type HB is Data:
  HB{bd: Nat, h: {Nat.pow(2n, 32n) == bd : Nat}}

def fot(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +k: String, +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +a: U32, +z: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hw: HB, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.fmt.one(w, KD.FKIND(tags, k), o, nalt, cp, i, NS.Rg{a, z}), m0,
    G.GSTR(FSO(k, WT.TX(len, t, NS.Rg{a, z}), tags, o, nalt, cp, i)), G.GOK(FSO(k, WT.TX(len, t, NS.Rg{a, z}), tags, o, nalt, cp, i))):
  match hw:
    case HB{+bd, +hbd}:
      fmt_one_t(len, t, d, hl, tags, k, o, nalt, cp, i, a, z, hp, bd, hbd, w, m0, r)

def fgo.e(+e: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +kt: Ss(), +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +he: {U32.is_eq(J(len, t, s, z), z) == e : Bool},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0),
  ih: @+s2: U32 -> @+h2: {Nat.is_le(n(s2), n(z)) == True{} : Bool} -> @-w2: NS.Sw -> @+m2: W.Wm -> W.Rel(len, t, w2, m2) ->
    S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), False{}, (w2, J(len, t, s2, z)), s2, z, o, nalt, cp, i, False{}), m2,
      G.JT(FSV(tags, o, nalt, cp, i, kt, VT(len, t, s2, z)), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, VT(len, t, s2, z))))) ->
  S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), e, (w, J(len, t, (J(len, t, s, z) + 1 : U32), z)), (J(len, t, s, z) + 1 : U32), z, o, nalt, cp, i, False{}), m0,
    G.JT(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z)), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z)))):
  match e:
    case True{}:
      +j = J(len, t, s, z)
      %Equal.sym(Ss(), VR(len, t, s, z), Nil{}, vr_last(len, t, s, z, he)) :
        S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), True{}, (w, J(len, t, (j + 1 : U32), z)), (j + 1 : U32), z, o, nalt, cp, i, False{}), m0,
          G.JT(FSV(tags, o, nalt, cp, i, kt, _), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, _)))
      fgo_done(len, t, tags, o, nalt, cp, i, kt, J(len, t, (j + 1 : U32), z), (j + 1 : U32), z, w, m0, r)
    case False{}:
      +j = J(len, t, s, z)
      +hlt = SC.lt_of(j, z, SC.j_hi(len, t, d, s, z, 58, hl, hsz, hz, {==}), he)
      %Equal.sym(Ss(), VR(len, t, s, z), VT(len, t, (j + 1 : U32), z), vr_next(len, t, d, hl, s, z, hsz, hz, hlt)) :
        S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), False{}, (w, J(len, t, (j + 1 : U32), z)), (j + 1 : U32), z, o, nalt, cp, i, False{}), m0,
          G.JT(FSV(tags, o, nalt, cp, i, kt, _), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, _)))
      ih((j + 1 : U32), SC.j1_le(len, t, d, j, z, hl, hz, hlt), w, m0, r)

def fgo.p(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +kt: Ss(), +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hw: HB,
  -w: NS.Sw, +m0: W.Wm,
  er: {NS.fone.w(w, (J(len, t, s, z) + 1 : U32), z) == (w, J(len, t, (J(len, t, s, z) + 1 : U32), z)) : NS.Sw & U32} & W.Rel(len, t, w, m0),
  ih: @+s2: U32 -> @+h2: {Nat.is_le(n(s2), n(z)) == True{} : Bool} -> @-w2: NS.Sw -> @+m2: W.Wm -> W.Rel(len, t, w2, m2) ->
    S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), False{}, (w2, J(len, t, s2, z)), s2, z, o, nalt, cp, i, False{}), m2,
      G.JT(FSV(tags, o, nalt, cp, i, kt, VT(len, t, s2, z)), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, VT(len, t, s2, z))))) ->
  S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), U32.is_eq(J(len, t, s, z), z), NS.fone.w(w, (J(len, t, s, z) + 1 : U32), z), (J(len, t, s, z) + 1 : U32), z, o, nalt, cp, i, False{}), m0,
    G.JT(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z)), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z)))):
  (ef, r1) = er
  +j = J(len, t, s, z)
  %Equal.sym(NS.Sw & U32, NS.fone.w(w, (j + 1 : U32), z), (w, J(len, t, (j + 1 : U32), z)), ef) :
    S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), U32.is_eq(j, z), _, (j + 1 : U32), z, o, nalt, cp, i, False{}), m0,
      G.JT(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z)), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z))))
  fgo.e(U32.is_eq(j, z), len, t, d, hl, tags, o, nalt, cp, i, kt, s, z, hsz, hz, {==}, w, m0, r1, ih)

def fgo.n(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +kt: Ss(), +s: U32, +z: U32,
  +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hw: HB,
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0),
  ih: @+s2: U32 -> @+h2: {Nat.is_le(n(s2), n(z)) == True{} : Bool} -> @-w2: NS.Sw -> @+m2: W.Wm -> W.Rel(len, t, w2, m2) ->
    S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), False{}, (w2, J(len, t, s2, z)), s2, z, o, nalt, cp, i, False{}), m2,
      G.JT(FSV(tags, o, nalt, cp, i, kt, VT(len, t, s2, z)), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, VT(len, t, s2, z))))) ->
  S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kt), U32.is_eq(J(len, t, s, z), z), NS.fone.w(w, (J(len, t, s, z) + 1 : U32), z), (J(len, t, s, z) + 1 : U32), z, o, nalt, cp, i, False{}), m0,
    G.JT(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z)), False{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z)))):
  fgo.p(len, t, d, hl, tags, o, nalt, cp, i, kt, s, z, hsz, hz, hw, w, m0, fone_w(len, t, w, m0, r, (J(len, t, s, z) + 1 : U32), z), ih)

law fgo_t:
  for +kss: Ss()
  for +s: U32
  for +first: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +tags: Tags()
  for +o: Bool
  for +nalt: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +z: U32
  for +hsz: {Nat.is_le(n(s), n(z)) == True{} : Bool}
  for +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool}
  for +hw: HB
  for -w: NS.Sw
  for +m0: W.Wm
  for r: W.Rel(len, t, w, m0)
  S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kss), False{}, (w, J(len, t, s, z)), s, z, o, nalt, cp, i, first), m0,
    G.JT(FSV(tags, o, nalt, cp, i, kss, VT(len, t, s, z)), first, ":"), G.JG(FSV(tags, o, nalt, cp, i, kss, VT(len, t, s, z))))

def fgo_t(kss, s, first, len, t, d, hl, tags, o, nalt, cp, i, z, hsz, hz, hw, w, m0, r):
  match kss:
    case Nil{}:
      %Equal.sym(Ss(), VT(len, t, s, z), Con{WT.TX(len, t, NS.Rg{s, J(len, t, s, z)}), VR(len, t, s, z)}, vt_first(len, t, d, hl, s, z, hsz, hz)) :
        S.WS(len, t, NS.fmt.go(Nil{}, False{}, (w, J(len, t, s, z)), s, z, o, nalt, cp, i, first), m0,
          G.JT(FSV(tags, o, nalt, cp, i, Nil{}, _), first, ":"), G.JG(FSV(tags, o, nalt, cp, i, Nil{}, _)))
      S.ws_fail(len, t, G.JT([B.Refuse{B.BadCount{}}], first, ":"), False{}, w, m0, r)
    case Con{+k, +kt}:
      +j = J(len, t, s, z)
      +x = {NS.Rg{s, j} : NS.Rg}
      +g = FSO(k, WT.TX(len, t, x), tags, o, nalt, cp, i)
      +R = FSV(tags, o, nalt, cp, i, kt, VR(len, t, s, z))
      +K = KD.FKIND(tags, k)
      +KT = KD.MAPF(tags, kt)
      -sw = NS.sep(w, first, 58)
      %Equal.sym(Ss(), VT(len, t, s, z), Con{WT.TX(len, t, x), VR(len, t, s, z)}, vt_first(len, t, d, hl, s, z, hsz, hz)) :
        S.WS(len, t, NS.fmt.go(KD.MAPF(tags, Con{k, kt}), False{}, (w, j), s, z, o, nalt, cp, i, first), m0,
          G.JT(FSV(tags, o, nalt, cp, i, Con{k, kt}, _), first, ":"), G.JG(FSV(tags, o, nalt, cp, i, Con{k, kt}, _)))
      S.ws_eq(len, t, NS.fmt.go(KT, U32.is_eq(j, z), NS.fone.w(NS.fmt.one(sw, K, o, nalt, cp, i, x), (j + 1 : U32), z), (j + 1 : U32), z, o, nalt, cp, i, False{}), m0,
        String.append(WT.SEPS(first, 58), String.append(G.GSTR(g), G.JT(R, False{}, ":"))), G.JT(Con{g, R}, first, ":"),
        Bool.and(True{}, Bool.and(G.GOK(g), G.JG(R))), G.JG(Con{g, R}),
        %Equal.sym(String, WT.SEPS(first, 58), G.PS(first, NR.chars([58])), seps_ps(first, 58)) : {String.append(_, String.append(G.GSTR(g), G.JT(R, False{}, ":"))) == G.JT(Con{g, R}, first, ":") : String}; {==},
        {==},
        S.ws_seq(len, t, sw, v => NS.fmt.go(KT, U32.is_eq(j, z), NS.fone.w(NS.fmt.one(v, K, o, nalt, cp, i, x), (j + 1 : U32), z), (j + 1 : U32), z, o, nalt, cp, i, False{}), m0,
          WT.SEPS(first, 58), String.append(G.GSTR(g), G.JT(R, False{}, ":")), True{}, Bool.and(G.GOK(g), G.JG(R)),
          S.ws_sep(len, t, d, hl, first, 58, {==}, w, m0, r),
          +m1 => r1 => S.ws_seq(len, t, NS.fmt.one(sw, K, o, nalt, cp, i, x), v => NS.fmt.go(KT, U32.is_eq(j, z), NS.fone.w(v, (j + 1 : U32), z), (j + 1 : U32), z, o, nalt, cp, i, False{}), m1,
            G.GSTR(g), G.JT(R, False{}, ":"), G.GOK(g), G.JG(R),
            fot(len, t, d, hl, tags, k, o, nalt, cp, i, s, j, pv_j(len, t, d, hl, s, z, hsz, hz), hw, sw, m1, r1),
            +m2 => r2 => fgo.n(len, t, d, hl, tags, o, nalt, cp, i, kt, s, z, hsz, hz, hw, NS.fmt.one(sw, K, o, nalt, cp, i, x), m2, r2,
              +s2 => +h2 => w2 => +m3 => r3 => fgo_t(kt, s2, False{}, len, t, d, hl, tags, o, nalt, cp, i, z, h2, hz, hw, w2, m3, r3)))))

def FS(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32) -> B.Got:
  B.Fmt.split(kss, WT.TX(len, t, NS.Rg{a, z}), tags, o, nalt, i)

def sm.k(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32,
  +hsz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hg: {G.JG(FSV(tags, o, nalt, GTO(kss, VT(len, t, a, z)), i, kss, VT(len, t, a, z))) == True{} : Bool}) ->
  ({G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)) == True{} : Bool} &
   {G.JT(FSV(tags, o, nalt, GTO(kss, VT(len, t, a, z)), i, kss, VT(len, t, a, z)), True{}, ":") == G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)) : String}):
  +L = FSV(tags, o, nalt, GTO(kss, VT(len, t, a, z)), i, kss, VT(len, t, a, z))
  +eF = {%Equal.sym(Ss(), String.split(WT.TX(len, t, NS.Rg{a, z}), ':'), VT(len, t, a, z), VL.split_chs(len, t, a, z, 58, hsz)) :
      {B.Got.join(B.Fmt.split.go(kss, _, tags, o, nalt, B.Gt.copies(B.Fmt.gt(kss, _)), i), ":") == B.Got{G.JT(L, True{}, ":")} : B.Got};
    G.join_t(L, ":", hg) : {FS(len, t, tags, kss, o, nalt, i, a, z) == B.Got{G.JT(L, True{}, ":")} : B.Got}}
  ({%Equal.sym(B.Got, FS(len, t, tags, kss, o, nalt, i, a, z), B.Got{G.JT(L, True{}, ":")}, eF) : {G.GOK(_) == True{} : Bool}; {==} : {G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)) == True{} : Bool}},
   {%Equal.sym(B.Got, FS(len, t, tags, kss, o, nalt, i, a, z), B.Got{G.JT(L, True{}, ":")}, eF) : {G.JT(L, True{}, ":") == G.GSTR(_) : String}; {==} : {G.JT(L, True{}, ":") == G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)) : String}})

def sm.in(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +kss: Ss(),
  +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +hw: HB,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool}) ->
  S.WS(len, t, NS.sample(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), W.Wm{W.V(l2, t2), p, ok},
    G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z))):
  +hsz = Equal.trans(Bool, Nat.is_le(n(a), n(z)), U32.is_le(a, z), True{}, Equal.sym(Bool, U32.is_le(a, z), Nat.is_le(n(a), n(z)), U.is_le_to_nat(a, z)), haz)
  +hzl = N.lt_to_le(n(z), n(len), hz)
  +j = J(len, t, a, z)
  +KS = KD.MAPF(tags, kss)
  +cp = GTO(kss, VT(len, t, a, z))
  +m0 = {W.Wm{W.V(l2, t2), p, ok} : W.Wm}
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, z, 58), (C.BT(len, t), j), SC.find_step(len, t, a, z, 58)) :
    S.WS(len, t, NS.sample.e(KS, NS.Rg{a, z}, _, C.BT(l2, t2), p, ok, o, nalt, i), m0, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)))
  %Equal.sym(D.Bytes & MN2(), NS.copies(KS, False{}, NS.hgt(KS), (C.BT(len, t), j), a, z), (C.BT(len, t), cp), cps_t(kss, a, len, t, d, hl, tags, z, hsz, hzl)) :
    S.WS(len, t, NS.sample.cp(KS, a, z, j, _, C.BT(l2, t2), p, ok, o, nalt, i), m0, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)))
  S.ws_imp(len, t, NS.fmt.go(KS, False{}, (NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, j), a, z, o, nalt, cp, i, True{}), m0,
    G.JT(FSV(tags, o, nalt, cp, i, kss, VT(len, t, a, z)), True{}, ":"), G.JG(FSV(tags, o, nalt, cp, i, kss, VT(len, t, a, z))),
    G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)),
    hg => sm.k(len, t, tags, kss, o, nalt, i, a, z, hsz, hg),
    fgo_t(kss, a, True{}, len, t, d, hl, tags, o, nalt, cp, i, z, hsz, hzl, hw, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, m0, W.refl(len, l2, t, t2, p, ok, h, hp)))

# A sample's column a .. z-1 in the record for ALT i of nalt: what
# B.Fmt.split gives.
def sample_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +kss: Ss(),
  +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.sample(w, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), m0, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z))):
  S.ws_at(len, t, w, v => NS.sample(v, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), m0, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)), r,
    +l2 => +t2 => +p => +ok => +h => +hp => sm.in(len, t, d, hl, tags, kss, o, nalt, i, a, z, haz, hz, HB{bd, hbd}, l2, t2, p, ok, h, hp))
