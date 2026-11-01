import Base
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Phase C, area "tan": every loop of NX.norm (norm_fix.bend) on the mirrors
# C.BT(bl, bt) (the line) and C.BT(wl, wt) (the window) hands both back, with
# the value its buffer-free twin in proof_c_defs.bend computes. Each byte
# read is C.at_pair_t.

# NX.ends's result for the flags e.
def LT(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, e: Q.EB) -> NX.Lt:
  match e:
    case Q.EB{eq, long}:
      NX.Lt{C.BT(bl, bt), C.BT(wl, wt), eq, long}

# The long flag.
def LG(e: Q.EB) -> Bool:
  match e:
    case Q.EB{eq, long}:
      long

# NX.right's result for the counters m.
def RRB(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, m: Maybe<&2, Q.K2>) -> NX.Rr:
  match m:
    case None{}:
      NX.RNeed{C.BT(bl, bt), C.BT(wl, wt)}
    case Some{Q.K2{k, tr}}:
      NX.RDone{C.BT(bl, bt), C.BT(wl, wt), k, tr}

law el_if_pair:
  for inw: Bool
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +iw: U32
  for +il: U32
  {NX.el.if(inw, C.BT(bl, bt), C.BT(wl, wt), iw, il) == NX.Rd{C.BT(bl, bt), C.BT(wl, wt), Q.EL.if(inw, bl, bt, wl, wt, iw, il)} : NX.Rd}

def el_if_pair(inw, bl, bt, wl, wt, iw, il):
  match inw:
    case True{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(wl, wt), iw), (C.BT(wl, wt), C.AT(wl, wt, iw)), C.at_pair_t(wl, wt, iw)) :
        {NX.el.w(C.BT(bl, bt), _) == NX.Rd{C.BT(bl, bt), C.BT(wl, wt), C.AT(wl, wt, iw)} : NX.Rd}
      {==}
    case False{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(bl, bt), il), (C.BT(bl, bt), C.AT(bl, bt, il)), C.at_pair_t(bl, bt, il)) :
        {NX.el.l(C.BT(wl, wt), _) == NX.Rd{C.BT(bl, bt), C.BT(wl, wt), C.AT(bl, bt, il)} : NX.Rd}
      {==}

law el_pair:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +a: NX.Ap
  for +k: U32
  for +j: U32
  for +p0: U32
  for +offu: U32
  {NX.el(C.BT(bl, bt), C.BT(wl, wt), a, k, j, p0, offu) == NX.Rd{C.BT(bl, bt), C.BT(wl, wt), Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)} : NX.Rd}

def el_pair(bl, bt, wl, wt, a, k, j, p0, offu):
  el_if_pair(U32.is_lt(j, k), bl, bt, wl, wt, ((((p0 - 1 : U32) - k : U32) + j : U32) - offu : U32), ((NX.Ap.st(a) + j : U32) - k : U32))

law ends_go_pair:
  for als: List<&2, NX.Ap>
  for +eq: Bool
  for +long: Bool
  for +z: U32
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +last: Bool
  for +p0: U32
  for +offu: U32
  {NX.ends.go(als, NX.Lt{C.BT(bl, bt), C.BT(wl, wt), eq, long}, z, k, tr, d, last, p0, offu) == LT(bl, bt, wl, wt, Q.ENDS.go(als, eq, long, z, bl, bt, wl, wt, k, tr, d, last, p0, offu)) : NX.Lt}

def ends_go_pair(als, eq, long, z, bl, bt, wl, wt, k, tr, d, last, p0, offu):
  match als:
    case Nil{}:
      {==}
    case +a <> t:
      +j = NX.ends.ix(last, a, tr, d)
      +x = Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)
      %Equal.sym(NX.Rd, NX.el(C.BT(bl, bt), C.BT(wl, wt), a, k, j, p0, offu), NX.Rd{C.BT(bl, bt), C.BT(wl, wt), x}, el_pair(bl, bt, wl, wt, a, k, j, p0, offu)) :
        {NX.ends.go(t, NX.ends.r(a, z, tr, d, eq, long, _), z, k, tr, d, last, p0, offu) == LT(bl, bt, wl, wt, Q.ENDS.go(a <> t, eq, long, z, bl, bt, wl, wt, k, tr, d, last, p0, offu)) : NX.Lt}
      ends_go_pair(t, eq && U32.is_eq(NX.code(x), z), long && U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32)), z, bl, bt, wl, wt, k, tr, d, last, p0, offu)

law ends_pair:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +last: Bool
  for +p0: U32
  for +offu: U32
  {NX.ends(als, C.BT(bl, bt), C.BT(wl, wt), k, tr, d, last, p0, offu) == LT(bl, bt, wl, wt, Q.ENDS(als, bl, bt, wl, wt, k, tr, d, last, p0, offu)) : NX.Lt}

def ends_pair(als, bl, bt, wl, wt, k, tr, d, last, p0, offu):
  match als:
    case Nil{}:
      {==}
    case +a <> t:
      +j = NX.ends.ix(last, a, tr, d)
      +x = Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)
      %Equal.sym(NX.Rd, NX.el(C.BT(bl, bt), C.BT(wl, wt), a, k, j, p0, offu), NX.Rd{C.BT(bl, bt), C.BT(wl, wt), x}, el_pair(bl, bt, wl, wt, a, k, j, p0, offu)) :
        {NX.ends.ref(t, a, k, tr, d, last, p0, offu, _) == LT(bl, bt, wl, wt, Q.ENDS(a <> t, bl, bt, wl, wt, k, tr, d, last, p0, offu)) : NX.Lt}
      ends_go_pair(t, True{}, U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32)), NX.code(x), bl, bt, wl, wt, k, tr, d, last, p0, offu)

law next_k_pair:
  for e: Q.EB
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +k: U32
  for +p0: U32
  for +offu: U32
  {NX.next.k(k, p0, offu, LT(bl, bt, wl, wt, e)) == NX.Na{C.BT(bl, bt), C.BT(wl, wt), Q.NEXT.k(k, p0, offu, e)} : NX.Na}

def next_k_pair(e, bl, bt, wl, wt, k, p0, offu):
  match e:
    case Q.EB{eq, long}:
      {==}

law next_pair:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +als: List<&2, NX.Ap>
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  {NX.next(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu, k, tr) == NX.Na{C.BT(bl, bt), C.BT(wl, wt), Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr)} : NX.Na}

def next_pair(bl, bt, wl, wt, als, p0, offu, k, tr):
  +e = Q.ENDS(als, bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu)
  %Equal.sym(NX.Lt, NX.ends(als, C.BT(bl, bt), C.BT(wl, wt), k, tr, 0n, True{}, p0, offu), LT(bl, bt, wl, wt, e), ends_pair(als, bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu)) :
    {NX.next.k(k, p0, offu, _) == NX.Na{C.BT(bl, bt), C.BT(wl, wt), Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr)} : NX.Na}
  next_k_pair(e, bl, bt, wl, wt, k, p0, offu)

law right_pair:
  for fuel: Nat
  for a: NX.Ak
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +als: List<&2, NX.Ap>
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  {NX.right(fuel, NX.Na{C.BT(bl, bt), C.BT(wl, wt), a}, als, p0, offu, k, tr) == RRB(bl, bt, wl, wt, Q.RIGHT(fuel, a, bl, bt, wl, wt, als, p0, offu, k, tr)) : NX.Rr}

def right_pair(fuel, a, bl, bt, wl, wt, als, p0, offu, k, tr):
  match fuel a:
    case 0n _:
      {==}
    case 1n+f NX.KStop{}:
      {==}
    case 1n+f NX.KNeed{}:
      {==}
    case 1n+f NX.KTrim{}:
      +t1 = (tr + 1 : U32)
      %Equal.sym(NX.Na, NX.next(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu, k, t1), NX.Na{C.BT(bl, bt), C.BT(wl, wt), Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, t1)}, next_pair(bl, bt, wl, wt, als, p0, offu, k, t1)) :
        {NX.right(f, _, als, p0, offu, k, t1) == RRB(bl, bt, wl, wt, Q.RIGHT(f, Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, t1), bl, bt, wl, wt, als, p0, offu, k, t1)) : NX.Rr}
      right_pair(f, Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, t1), bl, bt, wl, wt, als, p0, offu, k, t1)
    case 1n+f NX.KShift{}:
      +k1 = (k + 1 : U32)
      %Equal.sym(NX.Na, NX.next(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu, k1, tr), NX.Na{C.BT(bl, bt), C.BT(wl, wt), Q.NEXT(bl, bt, wl, wt, als, p0, offu, k1, tr)}, next_pair(bl, bt, wl, wt, als, p0, offu, k1, tr)) :
        {NX.right(f, _, als, p0, offu, k1, tr) == RRB(bl, bt, wl, wt, Q.RIGHT(f, Q.NEXT(bl, bt, wl, wt, als, p0, offu, k1, tr), bl, bt, wl, wt, als, p0, offu, k1, tr)) : NX.Rr}
      right_pair(f, Q.NEXT(bl, bt, wl, wt, als, p0, offu, k1, tr), bl, bt, wl, wt, als, p0, offu, k1, tr)

law leftk_pair:
  for e: Q.EB
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  {NX.left.k(LT(bl, bt, wl, wt, e)) == NX.Lt{C.BT(bl, bt), C.BT(wl, wt), Q.FIRSTS.k(e), LG(e)} : NX.Lt}

def leftk_pair(e, bl, bt, wl, wt):
  match e:
    case Q.EB{+eq, +long}:
      {==}

law firsts_pair:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +als: List<&2, NX.Ap>
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  {NX.firsts(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu, k, tr, d) == NX.Lt{C.BT(bl, bt), C.BT(wl, wt), Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, d), LG(Q.ENDS(als, bl, bt, wl, wt, k, tr, d, False{}, p0, offu))} : NX.Lt}

def firsts_pair(bl, bt, wl, wt, als, p0, offu, k, tr, d):
  +e = Q.ENDS(als, bl, bt, wl, wt, k, tr, d, False{}, p0, offu)
  %Equal.sym(NX.Lt, NX.ends(als, C.BT(bl, bt), C.BT(wl, wt), k, tr, d, False{}, p0, offu), LT(bl, bt, wl, wt, e), ends_pair(als, bl, bt, wl, wt, k, tr, d, False{}, p0, offu)) :
    {NX.left.k(_) == NX.Lt{C.BT(bl, bt), C.BT(wl, wt), Q.FIRSTS.k(e), LG(e)} : NX.Lt}
  leftk_pair(e, bl, bt, wl, wt)

law left_pair:
  for fuel: Nat
  for go: Bool
  for +l: Bool
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +als: List<&2, NX.Ap>
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  {NX.left(fuel, NX.Lt{C.BT(bl, bt), C.BT(wl, wt), go, l}, als, p0, offu, k, tr, d) == NX.Lr{C.BT(bl, bt), C.BT(wl, wt), Q.LEFT(fuel, go, bl, bt, wl, wt, als, p0, offu, k, tr, d)} : NX.Lr}

def left_pair(fuel, go, l, bl, bt, wl, wt, als, p0, offu, k, tr, d):
  match fuel go:
    case 0n _:
      {==}
    case 1n+f False{}:
      {==}
    case 1n+f True{}:
      +d1 = Nat.add(1n, d)
      +g = Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, d1)
      +l1 = LG(Q.ENDS(als, bl, bt, wl, wt, k, tr, d1, False{}, p0, offu))
      %Equal.sym(NX.Lt, NX.firsts(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu, k, tr, d1), NX.Lt{C.BT(bl, bt), C.BT(wl, wt), g, l1}, firsts_pair(bl, bt, wl, wt, als, p0, offu, k, tr, d1)) :
        {NX.left(f, _, als, p0, offu, k, tr, d1) == NX.Lr{C.BT(bl, bt), C.BT(wl, wt), Q.LEFT(f, g, bl, bt, wl, wt, als, p0, offu, k, tr, d1)} : NX.Lr}
      left_pair(f, g, l1, bl, bt, wl, wt, als, p0, offu, k, tr, d1)

law normr_pair:
  for m: Maybe<&2, Q.K2>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +als: List<&2, NX.Ap>
  for +p0: U32
  for +offu: U32
  {NX.norm.r(als, p0, offu, RRB(bl, bt, wl, wt, m)) == Q.NZB(bl, bt, wl, wt, Q.NZ.r(m, bl, bt, wl, wt, als, p0, offu)) : NX.Nr}

def normr_pair(m, bl, bt, wl, wt, als, p0, offu):
  match m:
    case None{}:
      {==}
    case Some{Q.K2{+k, +tr}}:
      +fu = Nat.add(U32.to_nat((p0 - k : U32)), NX.tot(als, tr))
      +g = Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, 0n)
      +l1 = LG(Q.ENDS(als, bl, bt, wl, wt, k, tr, 0n, False{}, p0, offu))
      %Equal.sym(NX.Lt, NX.firsts(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu, k, tr, 0n), NX.Lt{C.BT(bl, bt), C.BT(wl, wt), g, l1}, firsts_pair(bl, bt, wl, wt, als, p0, offu, k, tr, 0n)) :
        {NX.norm.l(k, tr, NX.left(fu, _, als, p0, offu, k, tr, 0n)) == NX.Nd{C.BT(bl, bt), C.BT(wl, wt), k, tr, Q.LEFT(fu, g, bl, bt, wl, wt, als, p0, offu, k, tr, 0n)} : NX.Nr}
      %Equal.sym(NX.Lr, NX.left(fu, NX.Lt{C.BT(bl, bt), C.BT(wl, wt), g, l1}, als, p0, offu, k, tr, 0n), NX.Lr{C.BT(bl, bt), C.BT(wl, wt), Q.LEFT(fu, g, bl, bt, wl, wt, als, p0, offu, k, tr, 0n)}, left_pair(fu, g, l1, bl, bt, wl, wt, als, p0, offu, k, tr, 0n)) :
        {NX.norm.l(k, tr, _) == NX.Nd{C.BT(bl, bt), C.BT(wl, wt), k, tr, Q.LEFT(fu, g, bl, bt, wl, wt, als, p0, offu, k, tr, 0n)} : NX.Nr}
      {==}

law norm_pair_t:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +als: List<&2, NX.Ap>
  for +p0: U32
  for +offu: U32
  {NX.norm(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu) == Q.NZB(bl, bt, wl, wt, Q.NZ(bl, bt, wl, wt, als, p0, offu)) : NX.Nr}

def norm_pair_t(bl, bt, wl, wt, als, p0, offu):
  +fu = Nat.add(U32.to_nat(p0), NX.tot(als, 0))
  +a = Q.NEXT(bl, bt, wl, wt, als, p0, offu, 0, 0)
  %Equal.sym(NX.Na, NX.next(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu, 0, 0), NX.Na{C.BT(bl, bt), C.BT(wl, wt), a}, next_pair(bl, bt, wl, wt, als, p0, offu, 0, 0)) :
    {NX.norm.r(als, p0, offu, NX.right(fu, _, als, p0, offu, 0, 0)) == Q.NZB(bl, bt, wl, wt, Q.NZ(bl, bt, wl, wt, als, p0, offu)) : NX.Nr}
  %Equal.sym(NX.Rr, NX.right(fu, NX.Na{C.BT(bl, bt), C.BT(wl, wt), a}, als, p0, offu, 0, 0), RRB(bl, bt, wl, wt, Q.RIGHT(fu, a, bl, bt, wl, wt, als, p0, offu, 0, 0)), right_pair(fu, a, bl, bt, wl, wt, als, p0, offu, 0, 0)) :
    {NX.norm.r(als, p0, offu, _) == Q.NZB(bl, bt, wl, wt, Q.NZ(bl, bt, wl, wt, als, p0, offu)) : NX.Nr}
  normr_pair(Q.RIGHT(fu, a, bl, bt, wl, wt, als, p0, offu, 0, 0), bl, bt, wl, wt, als, p0, offu)
