import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_cut.bend as K
import ./proof_s_scan.bend as SC
import ./proof_s_read.bend as RD
import ./proof_b_fasteq.bend as FE
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/fast.bend as F
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# What one pass over the line finds of the FORMAT keys (norm_split.bend's
# fkinds) and of the INFO entries (ikinds): one kind per key or entry, in
# order, read from its text. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def Rgs() -> Data:
  List<&2, NS.Rg>

def Ss() -> Data:
  List<&2, String>

def Fks() -> Data:
  List<&2, NS.Fk>

def Iks() -> Data:
  List<&2, NS.Ik>

def Tags() -> Data:
  List<&2, B.Tag>

# ---------------------------------------------------------------------------
# Reversing twice
# ---------------------------------------------------------------------------

law rr_fk:
  for +ys: Fks()
  for +acc: Fks()
  {NS.rev_fk(NS.rev_fk(ys, acc), Nil{}) == NS.rev_fk(acc, ys) : Fks()}

def rr_fk(ys, acc):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      rr_fk(r, Con{y, acc})

law rr_ik:
  for +ys: Iks()
  for +acc: Iks()
  {NS.rev_ik(NS.rev_ik(ys, acc), Nil{}) == NS.rev_ik(acc, ys) : Iks()}

def rr_ik(ys, acc):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      rr_ik(r, Con{y, acc})

# ---------------------------------------------------------------------------
# FORMAT keys
# ---------------------------------------------------------------------------

def FKIND(+tags: Tags(), +k: String) -> NS.Fk:
  Bool.pick(NS.Fk, String.eq(k, "GT"), NS.KGt{}, NS.fkind.num(B.Tags.find(tags, k)))

def MAPF(+tags: Tags(), ks: Ss()) -> Fks():
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, r}:
      Con{FKIND(tags, k), MAPF(tags, r)}

law fk_go:
  for +xs: Rgs()
  for +acc: Fks()
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +tags: Tags()
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hps: {K.ALLPV(len, xs) == True{} : Bool}
  {NS.fkinds.go(xs, (C.BT(len, t), acc), tags) == (C.BT(len, t), NS.rev_fk(MAPF(tags, K.TXS(len, t, xs)), acc)) : D.Bytes & Fks()}

def fk_go(xs, acc, len, t, d, tags, h, hps):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +hpx = N.and_true_l(W.PV(len, x), K.ALLPV(len, r), hps)
      +hpr = N.and_true_r(W.PV(len, x), K.ALLPV(len, r), hps)
      %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), x), (C.BT(len, t), WT.TX(len, t, x)), RD.txt_t(len, t, d, x, h, hpx)) :
        {NS.fkinds.go(r, NS.fkinds.cons(NS.fkind.k(_, tags), acc), tags) == (C.BT(len, t), NS.rev_fk(MAPF(tags, K.TXS(len, t, Con{x, r})), acc)) : D.Bytes & Fks()}
      fk_go(r, Con{FKIND(tags, WT.TX(len, t, x)), acc}, len, t, d, tags, h, hpr)

# The kinds of FORMAT keys xs, read from their text.
def fkinds_t(+xs: Rgs(), +len: U32, +t: AT.Tree<U32>, +d: Nat, +tags: Tags(),
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hps: {K.ALLPV(len, xs) == True{} : Bool}) ->
  {NS.fkinds(xs, C.BT(len, t), tags) == (C.BT(len, t), MAPF(tags, K.TXS(len, t, xs))) : D.Bytes & Fks()}:
  %Equal.sym(D.Bytes & Fks(), NS.fkinds.go(xs, (C.BT(len, t), Nil{}), tags), (C.BT(len, t), NS.rev_fk(MAPF(tags, K.TXS(len, t, xs)), Nil{})), fk_go(xs, Nil{}, len, t, d, tags, h, hps)) :
    {NS.fkinds.fin(_) == (C.BT(len, t), MAPF(tags, K.TXS(len, t, xs))) : D.Bytes & Fks()}
  %Equal.sym(Fks(), NS.rev_fk(NS.rev_fk(MAPF(tags, K.TXS(len, t, xs)), Nil{}), Nil{}), MAPF(tags, K.TXS(len, t, xs)), rr_fk(MAPF(tags, K.TXS(len, t, xs)), Nil{})) : {(C.BT(len, t), _) == (C.BT(len, t), MAPF(tags, K.TXS(len, t, xs))) : D.Bytes & Fks()}
  {==}

# ---------------------------------------------------------------------------
# INFO entries
# ---------------------------------------------------------------------------

# An entry a .. z-1: its first '=' (JE), its kind.
def JE(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> U32:
  SC.J(len, t, a, z, 61)

def IKIND(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +x: NS.Rg) -> NS.Ik:
  match x:
    case NS.Rg{+a, +z}:
      NS.ikind.v(U32.is_eq(z, JE(len, t, a, z)), NS.Rg{a, z}, JE(len, t, a, z), B.Tags.find(tags, WT.TX(len, t, NS.Rg{a, JE(len, t, a, z)})))

def MAPI(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), xs: Rgs()) -> Iks():
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      Con{IKIND(len, t, tags, x), MAPI(len, t, tags, r)}

def ikind_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +tags: Tags(), +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  {NS.ikind(C.BT(len, t), NS.Rg{a, z}, tags) == (C.BT(len, t), IKIND(len, t, tags, NS.Rg{a, z})) : D.Bytes & NS.Ik}:
  +haz = W.pv_a(len, a, z, hp)
  +hzl = W.pv_z(len, a, z, hp)
  +j = JE(len, t, a, z)
  +hpj = W.pv_mk(len, a, j, SC.j_lo(len, t, d, a, z, 61, h, haz, hzl, {==}), N.le_trans(n(j), n(z), n(len), SC.j_hi(len, t, d, a, z, 61, h, haz, hzl, {==}), hzl))
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, z, 61), (C.BT(len, t), j), SC.find_step(len, t, a, z, 61)) :
    {NS.ikind.at(NS.Rg{a, z}, _, tags) == (C.BT(len, t), IKIND(len, t, tags, NS.Rg{a, z})) : D.Bytes & NS.Ik}
  %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), NS.Rg{a, j}), (C.BT(len, t), WT.TX(len, t, NS.Rg{a, j})), RD.txt_t(len, t, d, NS.Rg{a, j}, h, hpj)) :
    {NS.ikind.k(NS.Rg{a, z}, j, _, tags) == (C.BT(len, t), IKIND(len, t, tags, NS.Rg{a, z})) : D.Bytes & NS.Ik}
  {==}

law ik_go:
  for +xs: Rgs()
  for +acc: Iks()
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +tags: Tags()
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hps: {K.ALLPV(len, xs) == True{} : Bool}
  {NS.ikinds.go(xs, (C.BT(len, t), acc), tags) == (C.BT(len, t), NS.rev_ik(MAPI(len, t, tags, xs), acc)) : D.Bytes & Iks()}

def ik_go(xs, acc, len, t, d, tags, h, hps):
  match xs:
    case Nil{}:
      {==}
    case Con{NS.Rg{+a, +z}, +r}:
      +hpx = N.and_true_l(W.PV(len, NS.Rg{a, z}), K.ALLPV(len, r), hps)
      +hpr = N.and_true_r(W.PV(len, NS.Rg{a, z}), K.ALLPV(len, r), hps)
      %Equal.sym(D.Bytes & NS.Ik, NS.ikind(C.BT(len, t), NS.Rg{a, z}, tags), (C.BT(len, t), IKIND(len, t, tags, NS.Rg{a, z})), ikind_t(len, t, d, tags, a, z, h, hpx)) :
        {NS.ikinds.go(r, NS.ikinds.cons(_, acc), tags) == (C.BT(len, t), NS.rev_ik(MAPI(len, t, tags, Con{NS.Rg{a, z}, r}), acc)) : D.Bytes & Iks()}
      ik_go(r, Con{IKIND(len, t, tags, NS.Rg{a, z}), acc}, len, t, d, tags, h, hpr)

# The kinds of INFO entries xs.
def ikinds_t(+xs: Rgs(), +len: U32, +t: AT.Tree<U32>, +d: Nat, +tags: Tags(),
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hps: {K.ALLPV(len, xs) == True{} : Bool}) ->
  {NS.ikinds(xs, C.BT(len, t), tags) == (C.BT(len, t), MAPI(len, t, tags, xs)) : D.Bytes & Iks()}:
  %Equal.sym(D.Bytes & Iks(), NS.ikinds.go(xs, (C.BT(len, t), Nil{}), tags), (C.BT(len, t), NS.rev_ik(MAPI(len, t, tags, xs), Nil{})), ik_go(xs, Nil{}, len, t, d, tags, h, hps)) :
    {NS.ikinds.fin(_) == (C.BT(len, t), MAPI(len, t, tags, xs)) : D.Bytes & Iks()}
  %Equal.sym(Iks(), NS.rev_ik(NS.rev_ik(MAPI(len, t, tags, xs), Nil{}), Nil{}), MAPI(len, t, tags, xs), rr_ik(MAPI(len, t, tags, xs), Nil{})) :
    {(C.BT(len, t), _) == (C.BT(len, t), MAPI(len, t, tags, xs)) : D.Bytes & Iks()}
  {==}
