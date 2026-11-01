import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./norm_fast.bend as NF
import ./proof_b_fasteq.bend as FE
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_b_cut_nat.bend as Z
import ./proof_b_cut_fx.bend as FX
import ./proof_b_cut_str.bend as S
import ./proof_b_cut_pos.bend as PO
import lawful-fields@0.1.0.0/proof_num.bend as LN

# The fast path's line tests on bytes (norm_fast.bend: NF.line = NF.pre of
# NF.cut) against the String path: when a line passes, its LF is the first
# one, the String code cuts the same fields, POS reads as written, and the
# alleles pass NF.alleles (proof_b_alleles.bend says what that means).
#
# Notation: a buffer is its mirror C.BT(len, t) (lawful-bytes); xs is its
# view; n(x) is U32.to_nat(x); fld(xs, a, b) is the text of bytes a .. b-1.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

# The text of bytes a .. b-1 (Norm.chars, one Char per byte).
def fld(+xs: List<&2, U32>, +a: Nat, +b: Nat) -> String:
  Norm.chars(D.slice(xs, a, Nat.sub(b, a)))

# The line's text before its LF, and the B.Line the machine makes of it.
def ltext(+xs: List<&2, U32>, +s: U32, +lf: U32) -> String:
  fld(xs, n(s), n(lf))

def lline(+xs: List<&2, U32>, +s: U32, +lf: U32) -> B.Line:
  Norm.line(ltext(xs, s, lf))

def lbody(+xs: List<&2, U32>, +s: U32, +lf: U32) -> String:
  B.Line.body(lline(xs, s, lf))

# What NF.line answers, without the buffer.
def Pr.p(r: NF.Pr) -> NF.Pre:
  match r:
    case NF.Pr{b, p}:
      p

def pre_of(+len: U32, +t: AT.Tree<U32>, +s: U32) -> NF.Pre:
  Pr.p(NF.line(C.BT(len, t), s))

# Field i's start: s for CHROM, else one past the previous end.
def nx(+e: U32) -> Nat:
  Nat.add(n(e), 1n)


# ---------------------------------------------------------------------------
# Helpers (the proofs are in proof_b_cut_*.bend)
# ---------------------------------------------------------------------------

def pre_eq(+len: U32, +t: AT.Tree<U32>, +s: U32) -> {pre_of(len, t, s) == M.PRE(len, t, s) : NF.Pre}:
  Equal.cong(NF.Pr, NF.Pre, r => Pr.p(r), NF.line(C.BT(len, t), s), NF.Pr{C.BT(len, t), M.PRE(len, t, s)}, M.line_t(len, t, s))

def hpre(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  hp: {pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}) -> {M.PRE(len, t, s) == V.P10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Pre}:
  Equal.trans(NF.Pre, M.PRE(len, t, s), pre_of(len, t, s), V.P10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf), Equal.sym(NF.Pre, pre_of(len, t, s), M.PRE(len, t, s), pre_eq(len, t, s)), hp)

# Field i's end, as a function of the cut.
def ce0(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{+e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      e0
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def ce1(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, +e1, e2, e3, e4, e5, e6, e7, lf}:
      e1
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def ce2(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, +e2, e3, e4, e5, e6, e7, lf}:
      e2
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def ce3(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, +e3, e4, e5, e6, e7, lf}:
      e3
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def ce4(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, e3, +e4, e5, e6, e7, lf}:
      e4
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def ce5(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, +e5, e6, e7, lf}:
      e5
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def ce6(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, +e6, e7, lf}:
      e6
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def ce7(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, e6, +e7, lf}:
      e7
    case NF.Short{}:
      0
    case NF.Part{}:
      0

def inc(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hlt: {Nat.is_lt(n(e), n(len)) == True{} : Bool}) -> {Nat.add(n(e), 1n) == n((e + 1 : U32)) : Nat}:
  Equal.sym(Nat, n((e + 1 : U32)), Nat.add(n(e), 1n), Z.nx1(len, e, Z.nxt(len, t, d, e, hok, hlt)))

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# NF.line hands the buffer back unchanged.
def line_pair(+len: U32, +t: AT.Tree<U32>, +s: U32) ->
  {NF.line(C.BT(len, t), s) == NF.Pr{C.BT(len, t), pre_of(len, t, s)} : NF.Pr}:
  %Equal.sym(NF.Pr, NF.line(C.BT(len, t), s), NF.Pr{C.BT(len, t), M.PRE(len, t, s)}, M.line_t(len, t, s)) :
    {_ == NF.Pr{C.BT(len, t), Pr.p(_)} : NF.Pr}
  {==}

def LFD(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  {D.first(xs(len, t), n(s), n(len), 10) == n(lf) : Nat}
  & ({Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  & ({Nat.is_le(n(s), n(e0)) == True{} : Bool}
  & ({Nat.is_lt(n(e0), n(e1)) == True{} : Bool}
  & ({Nat.is_lt(n(e1), n(e2)) == True{} : Bool}
  & ({Nat.is_lt(n(e2), n(e3)) == True{} : Bool}
  & ({Nat.is_lt(n(e3), n(e4)) == True{} : Bool}
  & ({Nat.is_lt(n(e4), n(e5)) == True{} : Bool}
  & ({Nat.is_lt(n(e5), n(e6)) == True{} : Bool}
  & ({Nat.is_lt(n(e6), n(e7)) == True{} : Bool}
  & {Nat.is_le(n(e7), n(lf)) == True{} : Bool})))))))))

def LFC(+len: U32, +t: AT.Tree<U32>, +s: U32, c: NF.Cut) -> Type:
  match c:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)
    case NF.Short{}:
      Unit
    case NF.Part{}:
      Unit

def pass_lf.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}, +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}, +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool}) ->
  LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  %hc : LFC(len, t, s, _)
  FX.lf_core(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hl)

# The line's LF is the first LF at or after s, inside the buffer, and the
# field ends are in order.
def pass_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}) ->
  {D.first(xs(len, t), n(s), n(len), 10) == n(lf) : Nat}
  & ({Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  & ({Nat.is_le(n(s), n(e0)) == True{} : Bool}
  & ({Nat.is_lt(n(e0), n(e1)) == True{} : Bool}
  & ({Nat.is_lt(n(e1), n(e2)) == True{} : Bool}
  & ({Nat.is_lt(n(e2), n(e3)) == True{} : Bool}
  & ({Nat.is_lt(n(e3), n(e4)) == True{} : Bool}
  & ({Nat.is_lt(n(e4), n(e5)) == True{} : Bool}
  & ({Nat.is_lt(n(e5), n(e6)) == True{} : Bool}
  & ({Nat.is_lt(n(e6), n(e7)) == True{} : Bool}
  & {Nat.is_le(n(e7), n(lf)) == True{} : Bool}))))))))):
  V.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf), V.inv(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      pass_lf.k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16))

def FDD(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  {J.pfs(lbody(xs(len, t), s, lf)) ==
    [fld(xs(len, t), n(s), n(e0)), fld(xs(len, t), nx(e0), n(e1)), fld(xs(len, t), nx(e1), n(e2)),
     fld(xs(len, t), nx(e2), n(e3)), fld(xs(len, t), nx(e3), n(e4)), fld(xs(len, t), nx(e4), n(e5)),
     fld(xs(len, t), nx(e5), n(e6)), B.Rec.field(J.pfs(lbody(xs(len, t), s, lf)), 7n)] : List<&2, String>}

def FDC(+len: U32, +t: AT.Tree<U32>, +s: U32, c: NF.Cut) -> Type:
  match c:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)
    case NF.Short{}:
      Unit
    case NF.Part{}:
      Unit

def CRc(+len: U32, +t: AT.Tree<U32>, c: NF.Cut) -> Type:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, e6, +e7, +lf}:
      {M.CRT(len, t, e7, lf) == True{} : Bool}
    case NF.Short{}:
      Unit
    case NF.Part{}:
      Unit

def NEc(+len: U32, +t: AT.Tree<U32>, c: NF.Cut) -> Type:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, +e6, +e7, lf}:
      {M.NE(len, t, (e6 + 1 : U32), e7) == True{} : Bool}
    case NF.Short{}:
      Unit
    case NF.Part{}:
      Unit

def pass_fields.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}, +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}, +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool},
  +hcr: {M.CRT(len, t, e7, lf) == True{} : Bool}) ->
  FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  %hc : FDC(len, t, s, _)
  FX.fd_core(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hl,
    AB.subst(NF.Cut, c => CRc(len, t, c), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), Equal.sym(NF.Cut, V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc), hcr))

# The String path cuts the same fields (INFO as J.pfs keeps it: "" when it
# has no END entry, else its text).
def pass_fields(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}) ->
  {J.pfs(lbody(xs(len, t), s, lf)) ==
    [fld(xs(len, t), n(s), n(e0)), fld(xs(len, t), nx(e0), n(e1)), fld(xs(len, t), nx(e1), n(e2)),
     fld(xs(len, t), nx(e2), n(e3)), fld(xs(len, t), nx(e3), n(e4)), fld(xs(len, t), nx(e4), n(e5)),
     fld(xs(len, t), nx(e5), n(e6)), B.Rec.field(J.pfs(lbody(xs(len, t), s, lf)), 7n)] : List<&2, String>}:
  V.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf), V.inv(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      pass_fields.k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h21))

def pass_pos.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}, +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut},
  +hnok: {M.Nv.ok(M.NUM(len, t, (e0 + 1 : U32), e1)) == True{} : Bool}, +hnv: {M.Nv.v(M.NUM(len, t, (e0 + 1 : U32), e1)) == pos : U32}) ->
  PO.PCT(len, t, nx(e0), n(e1), pos):
  +eq0 = Equal.cong(NF.Cut, U32, c => ce0(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc)
  +eq1 = Equal.cong(NF.Cut, U32, c => ce1(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc)
  +u0 = AB.subst(U32, z => {Nat.is_lt(n(z), n(len)) == True{} : Bool}, M.E0(len, t, s), e0, eq0, FX.ltE0(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14))
  +u1 = AB.subst(U32, z => {Nat.is_lt(n(z), n(len)) == True{} : Bool}, M.E1(len, t, s), e1, eq1, FX.ltE1(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14))
  +l1 = AB.subst(U32, z => {Nat.is_le(Nat.add(n(z), 1n), n(e1)) == True{} : Bool}, M.E0(len, t, s), e0, eq0,
    AB.subst(U32, z => {Nat.is_le(Nat.add(n(M.E0(len, t, s)), 1n), n(z)) == True{} : Bool}, M.E1(len, t, s), e1, eq1, FX.lE1(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14)))
  +i0 = Z.nx1(len, e0, Z.nxt(len, t, d, e0, hok, u0))
  +hft = AB.subst(Nat, z => {Nat.is_le(z, n(e1)) == True{} : Bool}, Nat.add(n(e0), 1n), n((e0 + 1 : U32)), Equal.sym(Nat, n((e0 + 1 : U32)), Nat.add(n(e0), 1n), i0), l1)
  AB.subst(Nat, z => PO.PCT(len, t, z, n(e1), pos), n((e0 + 1 : U32)), nx(e0), i0,
    PO.pos_core(len, t, d, (e0 + 1 : U32), e1, pos, Nat.pow(2n, 32n), U32.to_nat(429496729), {==}, {==}, LN.QM(Nat.pow(2n, 32n), {==}),
      hok, hft, N.lt_to_le(n(e1), n(len), u1), hnok, hnv))

# POS reads as the number the fast path read, written as Nat.show writes it.
def pass_pos(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}) ->
  {B.Pos.read(fld(xs(len, t), nx(e0), n(e1))) == Some{n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(n(pos)) == fld(xs(len, t), nx(e0), n(e1)) : String}
  & {Nat.is_eq(n(pos), 0n) == False{} : Bool}):
  V.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, PO.PCT(len, t, nx(e0), n(e1), pos), V.inv(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      pass_pos.k(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18))

def pass_alleles.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}, +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut},
  +hal: {M.AL(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == True{} : Bool}) ->
  {NF.alleles(C.BT(len, t), (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}
  & ({Nat.add(n(e2), 1n) == n((e2 + 1 : U32)) : Nat}
  & {Nat.add(n(e3), 1n) == n((e3 + 1 : U32)) : Nat}):
  +lt2 = AB.subst(U32, z => {Nat.is_lt(n(z), n(len)) == True{} : Bool}, M.E2(len, t, s), e2,
    Equal.cong(NF.Cut, U32, c => ce2(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc), FX.ltE2(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14))
  +lt3 = AB.subst(U32, z => {Nat.is_lt(n(z), n(len)) == True{} : Bool}, M.E3(len, t, s), e3,
    Equal.cong(NF.Cut, U32, c => ce3(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc), FX.ltE3(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14))
  (Equal.trans(D.Bytes & Bool, NF.alleles(C.BT(len, t), (e2 + 1 : U32), e3, (e3 + 1 : U32), e4), (C.BT(len, t), M.AL(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4)), (C.BT(len, t), True{}),
    M.alleles_t(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4), Equal.cong(Bool, D.Bytes & Bool, z => (C.BT(len, t), z), M.AL(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4), True{}, hal)),
    (inc(len, t, d, e2, hok, lt2), inc(len, t, d, e3, hok, lt3)))

# The alleles passed NF.alleles (REF is e2+1 .. e3-1, ALT e3+1 .. e4-1).
def pass_alleles(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}) ->
  {NF.alleles(C.BT(len, t), (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}
  & ({Nat.add(n(e2), 1n) == n((e2 + 1 : U32)) : Nat}
  & {Nat.add(n(e3), 1n) == n((e3 + 1 : U32)) : Nat}):
  V.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, {NF.alleles(C.BT(len, t), (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}
      & ({Nat.add(n(e2), 1n) == n((e2 + 1 : U32)) : Nat} & {Nat.add(n(e3), 1n) == n((e3 + 1 : U32)) : Nat}), V.inv(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      pass_alleles.k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h19))

# The line's text with its terminator is its bytes up to and with the LF
# (Norm.line moves a final CR into the terminator).
def line_text(+xs: List<&2, U32>, +s: U32, +lf: U32,
  hlf: {List.get(&2, U32, xs, n(lf)) == Some{10} : Maybe<&2, U32>},
  hsl: {Nat.is_le(n(s), n(lf)) == True{} : Bool}) ->
  {B.Line.text(lline(xs, s, lf)) == Norm.chars(D.slice(xs, n(s), Nat.sub(Nat.add(n(lf), 1n), n(s)))) : String}:
  +rhs = Norm.chars(D.slice(xs, n(s), Nat.sub(Nat.add(n(lf), 1n), n(s))))
  Equal.trans(String, B.Line.text(lline(xs, s, lf)), ltext(xs, s, lf) ++ "\n", rhs, S.ltext_nl(ltext(xs, s, lf)),
    Equal.sym(String, rhs, ltext(xs, s, lf) ++ "\n", S.fld_nl(xs, n(s), n(lf), hlf, hsl)))

# POS has at most 9 digits: it is below 10^9 (no U32 wrap in the fast path).
def pass_pos_small(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}) ->
  {U32.is_lt(pos, 1000000000) == True{} : Bool}:
  V.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, {U32.is_lt(pos, 1000000000) == True{} : Bool}, V.inv(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      PO.pos_small(len, t, (e0 + 1 : U32), e1, pos, Nat.pow(2n, 32n), U32.to_nat(429496729), {==}, {==}, LN.QM(Nat.pow(2n, 32n), {==}), h17, h18))
