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
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A sample's column in the record for ALT i (norm_split.bend's copies,
# fmt.one, fmt.go, sample, samples) writes what B.Fmt.split gives. Every
# variable is reusable.

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

def cp_nil(+len: U32, +t: AT.Tree<U32>, +f: NS.Fk, +fs: List<&2, NS.Fk>) ->
  {NS.copies(Con{f, fs}, Nil{}, C.BT(len, t)) == (C.BT(len, t), Some{2n}) : D.Bytes & Maybe<&2, Nat>}:
  match f:
    case NS.KGt{}:
      {==}
    case NS.KKeep{}:
      {==}
    case NS.KVal{+num}:
      {==}
    case NS.KBad{}:
      {==}

def cp_skip(+len: U32, +t: AT.Tree<U32>, +f: NS.Fk, +fs: List<&2, NS.Fk>, +v: NS.Rg, +vs: Rgs(), +hf: {is_kgt(f) == False{} : Bool}) ->
  {NS.copies(Con{f, fs}, Con{v, vs}, C.BT(len, t)) == NS.copies(fs, vs, C.BT(len, t)) : D.Bytes & Maybe<&2, Nat>}:
  match f:
    case NS.KGt{}:
      Empty.absurd({NS.copies(Con{NS.KGt{}, fs}, Con{v, vs}, C.BT(len, t)) == NS.copies(fs, vs, C.BT(len, t)) : D.Bytes & Maybe<&2, Nat>}, P.false_ne_true(Equal.sym(Bool, True{}, False{}, hf)))
    case NS.KKeep{}:
      {==}
    case NS.KVal{+num}:
      {==}
    case NS.KBad{}:
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

def cp.g(+g: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(),
  +k: String, +kt: Ss(), +a: U32, +z: U32, +vt: Rgs(), +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  ih: {NS.copies(KD.MAPF(tags, kt), vt, C.BT(len, t)) == (C.BT(len, t), GTO(kt, K.TXS(len, t, vt))) : D.Bytes & MN2()}) ->
  {NS.copies(Con{Bool.pick(NS.Fk, g, NS.KGt{}, NS.fkind.num(B.Tags.find(tags, k))), KD.MAPF(tags, kt)}, Con{NS.Rg{a, z}, vt}, C.BT(len, t)) ==
    (C.BT(len, t), B.Gt.copies(B.Fmt.gt.put(g, WT.TX(len, t, NS.Rg{a, z}), B.Fmt.gt(kt, K.TXS(len, t, vt))))) : D.Bytes & MN2()}:
  match g:
    case True{}:
      cp.v(len, t, d, hl, a, z, hp)
    case False{}:
      %Equal.sym(D.Bytes & MN2(), NS.copies(Con{NS.fkind.num(B.Tags.find(tags, k)), KD.MAPF(tags, kt)}, Con{NS.Rg{a, z}, vt}, C.BT(len, t)), NS.copies(KD.MAPF(tags, kt), vt, C.BT(len, t)), cp_skip(len, t, NS.fkind.num(B.Tags.find(tags, k)), KD.MAPF(tags, kt), NS.Rg{a, z}, vt, kgt_num(B.Tags.find(tags, k)))) :
        {_ == (C.BT(len, t), GTO(kt, K.TXS(len, t, vt))) : D.Bytes & MN2()}
      ih

law cp_t:
  for +ks: Ss()
  for +vs: Rgs()
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +tags: Tags()
  for +hps: {K.ALLPV(len, vs) == True{} : Bool}
  {NS.copies(KD.MAPF(tags, ks), vs, C.BT(len, t)) == (C.BT(len, t), GTO(ks, K.TXS(len, t, vs))) : D.Bytes & MN2()}

def cp_t(ks, vs, len, t, d, hl, tags, hps):
  match ks vs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+v, +vt}:
      {==}
    case Con{+k, +kt} Nil{}:
      cp_nil(len, t, KD.FKIND(tags, k), KD.MAPF(tags, kt))
    case Con{+k, +kt} Con{NS.Rg{+a, +z}, +vt}:
      +hp = N.and_true_l(W.PV(len, NS.Rg{a, z}), K.ALLPV(len, vt), hps)
      +hr = N.and_true_r(W.PV(len, NS.Rg{a, z}), K.ALLPV(len, vt), hps)
      cp.g(String.eq(k, "GT"), len, t, d, hl, tags, k, kt, a, z, vt, hp, cp_t(kt, vt, len, t, d, hl, tags, hr))

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

def FSG(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +o: Bool, +nalt: Nat, +cp: Maybe<&2, Nat>, +i: Nat, kss: Ss(), vs: Rgs()) -> G.Gs():
  B.Fmt.split.go(kss, K.TXS(len, t, vs), tags, o, nalt, cp, i)

def seps_ps(+first: Bool, +c: U32) -> {WT.SEPS(first, c) == G.PS(first, NR.chars([c])) : String}:
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

law fmt_go_t:
  for +kss: Ss()
  for +vs: Rgs()
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
  for +hps: {K.ALLPV(len, vs) == True{} : Bool}
  for +bd: Nat
  for +hbd: {Nat.pow(2n, 32n) == bd : Nat}
  for -w: NS.Sw
  for +m0: W.Wm
  for r: W.Rel(len, t, w, m0)
  S.WS(len, t, NS.fmt.go(KD.MAPF(tags, kss), vs, w, o, nalt, cp, i, first), m0,
    G.JT(FSG(len, t, tags, o, nalt, cp, i, kss, vs), first, ":"), G.JG(FSG(len, t, tags, o, nalt, cp, i, kss, vs)))

def fmt_go_t(kss, vs, first, len, t, d, hl, tags, o, nalt, cp, i, hps, bd, hbd, w, m0, r):
  match kss vs:
    case Nil{} Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Con{+k, +kt} Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Nil{} Con{+v, +vt}:
      S.ws_fail(len, t, G.JT([B.Refuse{B.BadCount{}}], first, ":"), False{}, w, m0, r)
    case Con{+k, +kt} Con{NS.Rg{+a, +z}, +vt}:
      +x = {NS.Rg{a, z} : NS.Rg}
      +hpx = N.and_true_l(W.PV(len, x), K.ALLPV(len, vt), hps)
      +hpr = N.and_true_r(W.PV(len, x), K.ALLPV(len, vt), hps)
      +g = FSO(k, WT.TX(len, t, x), tags, o, nalt, cp, i)
      +R = FSG(len, t, tags, o, nalt, cp, i, kt, vt)
      -sw = NS.sep(w, first, 58)
      S.ws_eq(len, t, NS.fmt.go(KD.MAPF(tags, kt), vt, NS.fmt.one(sw, KD.FKIND(tags, k), o, nalt, cp, i, x), o, nalt, cp, i, False{}), m0,
        String.append(WT.SEPS(first, 58), String.append(G.GSTR(g), G.JT(R, False{}, ":"))), G.JT(Con{g, R}, first, ":"),
        Bool.and(True{}, Bool.and(G.GOK(g), G.JG(R))), G.JG(Con{g, R}),
        %Equal.sym(String, WT.SEPS(first, 58), G.PS(first, NR.chars([58])), seps_ps(first, 58)) : {String.append(_, String.append(G.GSTR(g), G.JT(R, False{}, ":"))) == G.JT(Con{g, R}, first, ":") : String}; {==},
        {==},
        S.ws_seq(len, t, sw, v => NS.fmt.go(KD.MAPF(tags, kt), vt, NS.fmt.one(v, KD.FKIND(tags, k), o, nalt, cp, i, x), o, nalt, cp, i, False{}), m0,
          WT.SEPS(first, 58), String.append(G.GSTR(g), G.JT(R, False{}, ":")), True{}, Bool.and(G.GOK(g), G.JG(R)),
          S.ws_sep(len, t, d, hl, first, 58, {==}, w, m0, r),
          +m1 => r1 => S.ws_seq(len, t, NS.fmt.one(sw, KD.FKIND(tags, k), o, nalt, cp, i, x), v => NS.fmt.go(KD.MAPF(tags, kt), vt, v, o, nalt, cp, i, False{}), m1,
            G.GSTR(g), G.JT(R, False{}, ":"), G.GOK(g), G.JG(R),
            fmt_one_t(len, t, d, hl, tags, k, o, nalt, cp, i, a, z, hpx, bd, hbd, sw, m1, r1),
            +m2 => r2 => fmt_go_t(kt, vt, False{}, len, t, d, hl, tags, o, nalt, cp, i, hpr, bd, hbd, NS.fmt.one(sw, KD.FKIND(tags, k), o, nalt, cp, i, x), m2, r2))))

def FS(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32) -> B.Got:
  B.Fmt.split(kss, WT.TX(len, t, NS.Rg{a, z}), tags, o, nalt, i)

def sm.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +kss: Ss(),
  +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +hg: {G.JG(FSG(len, t, tags, o, nalt, GTO(kss, K.TXS(len, t, K.CUT(len, t, a, z, 58))), i, kss, K.CUT(len, t, a, z, 58))) == True{} : Bool}) ->
  ({G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)) == True{} : Bool} &
   {G.JT(FSG(len, t, tags, o, nalt, GTO(kss, K.TXS(len, t, K.CUT(len, t, a, z, 58))), i, kss, K.CUT(len, t, a, z, 58)), True{}, ":") == G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)) : String}):
  +XS = K.CUT(len, t, a, z, 58)
  +L = FSG(len, t, tags, o, nalt, GTO(kss, K.TXS(len, t, XS)), i, kss, XS)
  +eF = {%K.cut_tx(len, t, d, a, z, 58, hl, haz, hz, {==}) :
      {B.Got.join(B.Fmt.split.go(kss, _, tags, o, nalt, B.Gt.copies(B.Fmt.gt(kss, _)), i), ":") == B.Got{G.JT(L, True{}, ":")} : B.Got};
    G.join_t(L, ":", hg) : {FS(len, t, tags, kss, o, nalt, i, a, z) == B.Got{G.JT(L, True{}, ":")} : B.Got}}
  ({%Equal.sym(B.Got, FS(len, t, tags, kss, o, nalt, i, a, z), B.Got{G.JT(L, True{}, ":")}, eF) : {G.GOK(_) == True{} : Bool}; {==} : {G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)) == True{} : Bool}},
   {%Equal.sym(B.Got, FS(len, t, tags, kss, o, nalt, i, a, z), B.Got{G.JT(L, True{}, ":")}, eF) : {G.JT(L, True{}, ":") == G.GSTR(_) : String}; {==} : {G.JT(L, True{}, ":") == G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)) : String}})

def sm.in(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +kss: Ss(),
  +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool}) ->
  S.WS(len, t, NS.sample(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), W.Wm{W.V(l2, t2), p, ok},
    G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z))):
  +XS = K.CUT(len, t, a, z, 58)
  +cp = GTO(kss, K.TXS(len, t, XS))
  +hps = K.cut_pv(len, t, d, a, z, 58, hl, haz, hz, {==})
  %Equal.sym(D.Bytes & Rgs(), NS.cut(C.BT(len, t), NS.Rg{a, z}, 58), (C.BT(len, t), XS), K.cut_t(len, t, d, a, z, 58, hl, haz, N.lt_to_le(n(z), n(len), hz), {==})) :
    S.WS(len, t, NS.sample.k(KD.MAPF(tags, kss), _, C.BT(l2, t2), p, ok, o, nalt, i), W.Wm{W.V(l2, t2), p, ok}, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)))
  %Equal.sym(D.Bytes & MN2(), NS.copies(KD.MAPF(tags, kss), XS, C.BT(len, t)), (C.BT(len, t), cp), cp_t(kss, XS, len, t, d, hl, tags, hps)) :
    S.WS(len, t, NS.sample.cp(KD.MAPF(tags, kss), XS, _, C.BT(l2, t2), p, ok, o, nalt, i), W.Wm{W.V(l2, t2), p, ok}, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)))
  S.ws_imp(len, t, NS.fmt.go(KD.MAPF(tags, kss), XS, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, o, nalt, cp, i, True{}), W.Wm{W.V(l2, t2), p, ok},
    G.JT(FSG(len, t, tags, o, nalt, cp, i, kss, XS), True{}, ":"), G.JG(FSG(len, t, tags, o, nalt, cp, i, kss, XS)),
    G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)),
    hg => sm.k(len, t, d, hl, tags, kss, o, nalt, i, a, z, haz, hz, hg),
    fmt_go_t(kss, XS, True{}, len, t, d, hl, tags, o, nalt, cp, i, hps, bd, hbd, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, W.Wm{W.V(l2, t2), p, ok}, W.refl(len, l2, t, t2, p, ok, h, hp)))

# A sample's column a .. z-1 in the record for ALT i of nalt: what
# B.Fmt.split gives.
def sample_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +tags: Tags(), +kss: Ss(),
  +o: Bool, +nalt: Nat, +i: Nat, +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.sample(w, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), m0, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z))):
  S.ws_at(len, t, w, v => NS.sample(v, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), m0, G.GSTR(FS(len, t, tags, kss, o, nalt, i, a, z)), G.GOK(FS(len, t, tags, kss, o, nalt, i, a, z)), r,
    +l2 => +t2 => +p => +ok => +h => +hp => sm.in(len, t, d, hl, tags, kss, o, nalt, i, a, z, haz, hz, bd, hbd, l2, t2, p, ok, h, hp))
