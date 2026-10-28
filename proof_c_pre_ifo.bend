import Base
import ./types.bend as B
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./proof_c_defs.bend as Q
import ./proof_b_cut.bend as CU
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_c_pre_pair.bend as P
import ./proof_c_pre_inf.bend as IN
import ./proof_c_pre_key.bend as KY
import ./proof_window_info.bend as W
import ./proof_b_alleles_loop.bend as LP
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N

# fix_info from its parts: INFO in the full field split is INFO's bytes
# (proof_c_pre_inf.bend), with no END entry (J.scan, then
# proof_window_info.bend's scan_eq) and none of the stale keys
# (proof_c_pre_key.bend).

# Field 7 of the String path's split.
def F7(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> String:
  B.Rec.field(B.Rec.fields(CU.lbody(Q.xs(len, t), s, lf)), 7n)

def INFO(+len: U32, +t: AT.Tree<U32>, +e6: U32, +e7: U32) -> String:
  Q.fld(Q.xs(len, t), Q.nx(e6), Q.n(e7))

def IGe(+len: U32, +t: AT.Tree<U32>, +s: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  {F7(len, t, s, lf) == INFO(len, t, e6, e7) : String} & {J.scan(INFO(len, t, e6, e7), True{}) == Nil{} : List<&2, Maybe<&2, Nat>>}

def IGC(+len: U32, +t: AT.Tree<U32>, +s: U32, c: NF.Cut) -> Type:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, +e6, +e7, +lf}:
      IGe(len, t, s, e6, e7, lf)
    case NF.Short{}:
      Unit
    case NF.Part{}:
      Unit

def info_k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool},
  +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut},
  +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool},
  +hne: {M.NE(len, t, (e6 + 1 : U32), e7) == True{} : Bool}, +hcr: {M.CRT(len, t, e7, lf) == True{} : Bool}) ->
  IGe(len, t, s, e6, e7, lf):
  %hc : IGC(len, t, s, _)
  IN.ifd_core(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hl,
    AB.subst(NF.Cut, c => CU.CRc(len, t, c), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), Equal.sym(NF.Cut, V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc), hcr),
    AB.subst(NF.Cut, c => CU.NEc(len, t, c), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), Equal.sym(NF.Cut, V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc), hne))

# ---------------------------------------------------------------------------
# No END entry
# ---------------------------------------------------------------------------

def isNilM(l: List<&2, Maybe<&2, Nat>>) -> Type:
  match l:
    case Nil{}:
      Unit
    case x <> r:
      Empty

def cn(+x: Maybe<&2, Nat>, +r: List<&2, Maybe<&2, Nat>>, +h: {x <> r == Nil{} : List<&2, Maybe<&2, Nat>>}) -> Empty:
  %Equal.sym(List<&2, Maybe<&2, Nat>>, x <> r, Nil{}, h) : isNilM(_)
  Unit{}

def eh_k(+b: Bool, +p: String, +q: List<&2, String>,
  +he: {B.Info.ends.put(b, p, B.Info.ends.go(q)) == Nil{} : List<&2, Maybe<&2, Nat>>},
  ih: {B.Info.ends.go(q) == Nil{} : List<&2, Maybe<&2, Nat>>} -> {B.Info.has.go(q, "END") == False{} : Bool}) ->
  {Bool.or(b, B.Info.has.go(q, "END")) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, cn(B.Pos.read(String.drop(p, 4n)), B.Info.ends.go(q), he))
    case False{}:
      ih(he)

def ends_has(+ps: List<&2, String>, +he: {B.Info.ends.go(ps) == Nil{} : List<&2, Maybe<&2, Nat>>}) -> {B.Info.has.go(ps, "END") == False{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +q:
      eh_k(String.eq(B.Info.key(p), "END"), p, q, he, h2 => ends_has(q, h2))

def end_has(+s: String, +h: {J.scan(s, True{}) == Nil{} : List<&2, Maybe<&2, Nat>>}) -> {B.Info.has(s, "END") == False{} : Bool}:
  ends_has(String.split(s, ';'), Equal.trans(List<&2, Maybe<&2, Nat>>, B.Info.ends.go(W.semi(s)), J.scan(s, True{}), Nil{},
    Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan(s, True{}), W.R(s, True{}), W.scan_eq(s, True{})), h))

# ---------------------------------------------------------------------------
# All five keys
# ---------------------------------------------------------------------------

def NOK(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> Type:
  {B.Info.has(F7(len, t, s, lf), "END") == False{} : Bool}
  & ({B.Info.has(F7(len, t, s, lf), "CIGAR") == False{} : Bool}
  & ({B.Info.has(F7(len, t, s, lf), "HOMLEN") == False{} : Bool}
  & ({B.Info.has(F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}
  & {B.Info.has(F7(len, t, s, lf), "AA") == False{} : Bool})))

def kk(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hf7: {F7(len, t, s, lf) == INFO(len, t, e6, e7) : String},
  +h6: {Nat.is_lt(Q.n(e6), Q.n(len)) == True{} : Bool}, +h67: {Nat.is_le(Q.n((e6 + 1 : U32)), Q.n(e7)) == True{} : Bool}, +h7: {Nat.is_le(Q.n(e7), Q.n(len)) == True{} : Bool},
  +g9: {P.NOST(len, t, (e6 + 1 : U32), e7) == True{} : Bool}) ->
  {B.Info.has(F7(len, t, s, lf), KY.KS(i)) == False{} : Bool}:
  AB.subst(String, z => {B.Info.has(z, KY.KS(i)) == False{} : Bool}, INFO(len, t, e6, e7), F7(len, t, s, lf), Equal.sym(String, F7(len, t, s, lf), INFO(len, t, e6, e7), hf7),
    KY.info_key(i, len, t, d, e6, e7, h, h6, h67, h7, g9))

def info_fin(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h6: {Nat.is_lt(Q.n(e6), Q.n(len)) == True{} : Bool}, +h67: {Nat.is_le(Q.n((e6 + 1 : U32)), Q.n(e7)) == True{} : Bool}, +h7: {Nat.is_le(Q.n(e7), Q.n(len)) == True{} : Bool},
  +g9: {P.NOST(len, t, (e6 + 1 : U32), e7) == True{} : Bool}, r: IGe(len, t, s, e6, e7, lf)) ->
  NOK(len, t, s, lf):
  match r:
    case (+hf7, hsc):
      (AB.subst(String, z => {B.Info.has(z, "END") == False{} : Bool}, INFO(len, t, e6, e7), F7(len, t, s, lf), Equal.sym(String, F7(len, t, s, lf), INFO(len, t, e6, e7), hf7), end_has(INFO(len, t, e6, e7), hsc)),
        (kk(0n, len, t, d, s, e6, e7, lf, h, hf7, h6, h67, h7, g9),
        (kk(1n, len, t, d, s, e6, e7, lf, h, hf7, h6, h67, h7, g9),
        (kk(2n, len, t, d, s, e6, e7, lf, h, hf7, h6, h67, h7, g9),
        kk(3n, len, t, d, s, e6, e7, lf, h, hf7, h6, h67, h7, g9)))))

def bnd6.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e6: U32, +e7: U32, +lf: U32, -G: Type, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +b1: {Nat.is_lt(Q.n(lf), Q.n(len)) == True{} : Bool}, +b9: {Nat.is_lt(Q.n(e6), Q.n(e7)) == True{} : Bool}, +b10: {Nat.is_le(Q.n(e7), Q.n(lf)) == True{} : Bool},
  k: {Nat.is_lt(Q.n(e6), Q.n(len)) == True{} : Bool} -> {Nat.is_le(Q.n((e6 + 1 : U32)), Q.n(e7)) == True{} : Bool} -> {Nat.is_le(Q.n(e7), Q.n(len)) == True{} : Bool} -> G) -> G:
  +h7 = N.le_trans(Q.n(e7), Q.n(lf), Q.n(len), b10, N.lt_to_le(Q.n(lf), Q.n(len), b1))
  +h6 = N.lt_le_trans(Q.n(e6), Q.n(e7), Q.n(len), b9, h7)
  +i6 = Equal.trans(Nat, Q.n((e6 + 1 : U32)), Nat.add(Q.n(e6), 1n), 1n+Q.n(e6), LP.inc_len(len, t, d, e6, h, h6), N.add_one(Q.n(e6)))
  k(h6, AB.subst(Nat, z => {Nat.is_le(z, Q.n(e7)) == True{} : Bool}, 1n+Q.n(e6), Q.n((e6 + 1 : U32)), Equal.sym(Nat, Q.n((e6 + 1 : U32)), 1n+Q.n(e6), i6),
    Equal.trans(Bool, Nat.is_le(1n+Q.n(e6), Q.n(e7)), Nat.is_lt(Q.n(e6), Q.n(e7)), True{}, N.le_succ_lt(Q.n(e6), Q.n(e7)), b9)), h7)

# The bounds info_fin needs, from the line's LF and field ends.
def bnd6(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, -G: Type, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  r: CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  k: {Nat.is_lt(Q.n(e6), Q.n(len)) == True{} : Bool} -> {Nat.is_le(Q.n((e6 + 1 : U32)), Q.n(e7)) == True{} : Bool} -> {Nat.is_le(Q.n(e7), Q.n(len)) == True{} : Bool} -> G) -> G:
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
                                          bnd6.k(len, t, d, e6, e7, lf, G, h, b1, b9, b10, k)
