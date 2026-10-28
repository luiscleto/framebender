import Base
import ./norm_fast.bend as NF
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_b_cut.bend as CU
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_b_cut_nat.bend as Z
import ./proof_b_cut_fx.bend as FX
import ./proof_b_cut_pos.bend as PO
import ./proof_c_pre_pair.bend as P
import ./proof_c_pre_inv.bend as I
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-fields/proof_num.bend as LN
import ../lawful-words/proof_nat.bend as N

# The cut, POS, CR and tab facts of a passed line, from phase B's lemmas.

def hfx(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  {P.FX(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}:
  Equal.trans(NX.Fp, P.FX(len, t, s), Q.fx_of(len, t, s), NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up},
    Equal.sym(NX.Fp, Q.fx_of(len, t, s), P.FX(len, t, s), Equal.cong(NX.Fr, NX.Fp, r => Q.Fr.p(r), NX.line(C.BT(len, t), s), NX.Fr{C.BT(len, t), P.FX(len, t, s)}, P.line_t(len, t, s))), hp)

def invx(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  I.INV(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up):
  I.inv(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hfx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp))

def POS4(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +pos: U32) -> Type:
  {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}
  & ({Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}
  & {U32.is_lt(pos, 1000000000) == True{} : Bool}))

def pos4(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +pos: U32, r: PO.PCT(len, t, Q.nx(e0), Q.n(e1), pos),
  +hs: {U32.is_lt(pos, 1000000000) == True{} : Bool}) -> POS4(len, t, e0, e1, pos):
  match r:
    case (a, r2):
      match r2:
        case (b, c):
          (a, (b, (c, hs)))

def TAB(+len: U32, +t: AT.Tree<U32>, +e: U32) -> Type:
  {List.get(&2, U32, Q.xs(len, t), Q.n(e)) == Some{9} : Maybe<&2, U32>}

def tab_e(+len: U32, +t: AT.Tree<U32>, +x: U32, +e: U32, +hx: {x == e : U32}, h: TAB(len, t, x)) -> TAB(len, t, e):
  AB.subst(U32, z => TAB(len, t, z), x, e, hx, h)

def bnd.k(+len: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, -G: Type,
  +b1: {Nat.is_lt(Q.n(lf), Q.n(len)) == True{} : Bool}, +b5: {Nat.is_lt(Q.n(e2), Q.n(e3)) == True{} : Bool}, +b6: {Nat.is_lt(Q.n(e3), Q.n(e4)) == True{} : Bool},
  +b7: {Nat.is_lt(Q.n(e4), Q.n(e5)) == True{} : Bool}, +b8: {Nat.is_lt(Q.n(e5), Q.n(e6)) == True{} : Bool}, +b9: {Nat.is_lt(Q.n(e6), Q.n(e7)) == True{} : Bool},
  +b10: {Nat.is_le(Q.n(e7), Q.n(lf)) == True{} : Bool},
  k: {Nat.is_lt(Q.n(e2), Q.n(len)) == True{} : Bool} -> {Nat.is_lt(Q.n(e3), Q.n(len)) == True{} : Bool} -> {Nat.is_le(Q.n(e4), Q.n(lf)) == True{} : Bool} -> {Nat.is_lt(Q.n(lf), Q.n(len)) == True{} : Bool} -> G) -> G:
  +h4l = N.lt_to_le(Q.n(e4), Q.n(lf), N.lt_le_trans(Q.n(e4), Q.n(e7), Q.n(lf), N.lt_trans(Q.n(e4), Q.n(e5), Q.n(e7), b7, N.lt_trans(Q.n(e5), Q.n(e6), Q.n(e7), b8, b9)), b10))
  +hl3 = N.lt_trans(Q.n(e3), Q.n(e4), Q.n(len), b6, N.le_lt_trans(Q.n(e4), Q.n(lf), Q.n(len), h4l, b1))
  k(N.lt_trans(Q.n(e2), Q.n(e3), Q.n(len), b5, hl3), hl3, h4l, b1)

# The bounds fix_als needs, from the line's LF and field ends.
def bnd(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, -G: Type,
  r: CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  k: {Nat.is_lt(Q.n(e2), Q.n(len)) == True{} : Bool} -> {Nat.is_lt(Q.n(e3), Q.n(len)) == True{} : Bool} -> {Nat.is_le(Q.n(e4), Q.n(lf)) == True{} : Bool} -> {Nat.is_lt(Q.n(lf), Q.n(len)) == True{} : Bool} -> G) -> G:
  match r:
    case (b0, r1):
      match r1:
        case (b1, r2):
          match r2:
            case (b2, r3):
              match r3:
                case (b3, r4):
                  match r4:
                    case (b4, r5):
                      match r5:
                        case (b5, r6):
                          match r6:
                            case (b6, r7):
                              match r7:
                                case (b7, r8):
                                  match r8:
                                    case (b8, r9):
                                      match r9:
                                        case (b9, b10):
                                          bnd.k(len, e2, e3, e4, e5, e6, e7, lf, G, b1, b5, b6, b7, b8, b9, b10, k)
