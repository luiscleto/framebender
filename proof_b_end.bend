import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./proof_c_defs.bend as Q
import ./proof_fast.bend as PF
import ./proof_b_cut.bend as CU
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_b_end_inf.bend as IE
import ./proof_b_end_key.bend as EK
import ./proof_c_pre_ifo.bend as IF
import ./proof_window_info.bend as W
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_b_cut_nat.bend as Z

# INFO/END on the fast path: when a line passes NF.line, INFO as the String
# path keeps it (field 7 of J.pfs) passes J.end_ok for POS + len(REF) - 1.
# The chain: J.pfs's INFO reads as the full split's (pfs_end), which is
# INFO's bytes (proof_b_end_inf.bend), on which NF.ends passing gives
# B.Info.end_ok (proof_b_end_key.bend), which is J.end_ok
# (proof_window_info.bend's end_ok_eq).

# J.pfs keeps INFO so that the END check reads the same.
def pe.k(+g: J.C7, +body: String, +e: Nat, +hg: {PF.gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}) ->
  {J.end_ok(B.Rec.field(J.pfs.g(g, body), 7n), e) == J.end_ok(B.Rec.field(B.Rec.fields(body), 7n), e) : Bool}:
  match g:
    case J.Short{}:
      {==}
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      %hg : {J.end_ok(J.info.if(J.noend(r), r), e) == J.end_ok(B.Rec.field(_, 7n), e) : Bool}
      %Equal.sym(List<&2, String>, String.split(r, '\t'), J.Cut.f(J.cut(r)) <> PF.ctail(J.cut(r)), PF.split_ft(r)) :
        {J.end_ok(J.info.if(J.noend(r), r), e) == J.end_ok(B.Rec.field(f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> _, 7n), e) : Bool}
      PF.info_end(r, e)

def pfs_end(+body: String, +e: Nat) -> {J.end_ok(B.Rec.field(J.pfs(body), 7n), e) == J.end_ok(B.Rec.field(B.Rec.fields(body), 7n), e) : Bool}:
  pe.k(J.c7(body), body, e, PF.c7_split(body))

def IGE(+len: U32, +t: AT.Tree<U32>, +s: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  {IF.F7(len, t, s, lf) == IF.INFO(len, t, e6, e7) : String}

def IGCe(+len: U32, +t: AT.Tree<U32>, +s: U32, c: NF.Cut) -> Type:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, +e6, +e7, +lf}:
      IGE(len, t, s, e6, e7, lf)
    case NF.Short{}:
      Unit
    case NF.Part{}:
      Unit

# Field 7 of the full split is INFO's bytes (proof_c_pre_ifo.bend's info_k
# without its no-END hypothesis).
def info_k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool},
  +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut},
  +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool},
  +hcr: {M.CRT(len, t, e7, lf) == True{} : Bool}) ->
  IGE(len, t, s, e6, e7, lf):
  %hc : IGCe(len, t, s, _)
  IE.ifd_core(len, t, d, s, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hl,
    AB.subst(NF.Cut, c => CU.CRc(len, t, c), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), Equal.sym(NF.Cut, V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), hc), hcr))

def PEG(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e2: U32, +e3: U32, +lf: U32) -> Type:
  {J.end_ok(B.Rec.field(J.pfs(CU.lbody(Q.xs(len, t), s, lf)), 7n), EK.EV0(pos, (e3 - e2 - 1 : U32))) == True{} : Bool}

def ige2(+len: U32, +t: AT.Tree<U32>, +s: U32, +e6: U32, +e7: U32, +lf: U32, r: IF.IGe(len, t, s, e6, e7, lf)) ->
  {J.scan(IF.INFO(len, t, e6, e7), True{}) == Nil{} : List<&2, Maybe<&2, Nat>>}:
  match r:
    case (a, b):
      b

def iend(+ne: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool},
  +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut},
  +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool},
  +hne: {M.EKQ(len, t, (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32)) == True{} : Bool}, +hcr: {M.CRT(len, t, e7, lf) == True{} : Bool},
  +hneq: {M.NE(len, t, (e6 + 1 : U32), e7) == ne : Bool},
  +b6: {Nat.is_lt(Q.n(e6), Q.n(len)) == True{} : Bool}, +b67: {Nat.is_le(Q.n((e6 + 1 : U32)), Q.n(e7)) == True{} : Bool}, +b7: {Nat.is_le(Q.n(e7), Q.n(len)) == True{} : Bool}) ->
  {J.end_ok(IF.INFO(len, t, e6, e7), EK.EV0(pos, (e3 - e2 - 1 : U32))) == True{} : Bool}:
  match ne:
    case True{}:
      AB.subst(List<&2, Maybe<&2, Nat>>, z => {B.Info.end_ok.go(z, EK.EV0(pos, (e3 - e2 - 1 : U32))) == True{} : Bool}, Nil{}, J.scan(IF.INFO(len, t, e6, e7), True{}),
        Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan(IF.INFO(len, t, e6, e7), True{}), Nil{}, ige2(len, t, s, e6, e7, lf, IF.info_k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hc, hl, hneq, hcr))), {==})
    case False{}:
      Equal.trans(Bool, J.end_ok(IF.INFO(len, t, e6, e7), EK.EV0(pos, (e3 - e2 - 1 : U32))), B.Info.end_ok(IF.INFO(len, t, e6, e7), EK.EV0(pos, (e3 - e2 - 1 : U32))), True{},
        W.end_ok_eq(IF.INFO(len, t, e6, e7), EK.EV0(pos, (e3 - e2 - 1 : U32))),
        EK.info_end(len, t, d, e6, e7, pos, (e3 - e2 - 1 : U32), hok, b6, b67, b7,
          AB.subst(Bool, z => {M.EKI(z, len, t, (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32)) == True{} : Bool}, M.NE(len, t, (e6 + 1 : U32), e7), False{}, hneq, hne)))

def pass_end.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool},
  +hc: {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut},
  +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool},
  +hne: {M.EKQ(len, t, (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32)) == True{} : Bool}, +hcr: {M.CRT(len, t, e7, lf) == True{} : Bool},
  +b6: {Nat.is_lt(Q.n(e6), Q.n(len)) == True{} : Bool}, +b67: {Nat.is_le(Q.n((e6 + 1 : U32)), Q.n(e7)) == True{} : Bool}, +b7: {Nat.is_le(Q.n(e7), Q.n(len)) == True{} : Bool}) ->
  PEG(len, t, s, pos, e2, e3, lf):
  +Ev = EK.EV0(pos, (e3 - e2 - 1 : U32))
  +body = CU.lbody(Q.xs(len, t), s, lf)
  +F7 = IF.F7(len, t, s, lf)
  +I7 = IF.INFO(len, t, e6, e7)
  Equal.trans(Bool, J.end_ok(B.Rec.field(J.pfs(body), 7n), Ev), J.end_ok(F7, Ev), True{}, pfs_end(body, Ev),
    Equal.trans(Bool, J.end_ok(F7, Ev), J.end_ok(I7, Ev), True{},
      Equal.cong(String, Bool, z => J.end_ok(z, Ev), F7, I7, info_k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hc, hl, hcr)),
      iend(M.NE(len, t, (e6 + 1 : U32), e7), len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hc, hl, hne, hcr, {==}, b6, b67, b7)))

# A line that passes NF.line: INFO, as J.pfs keeps it, passes the END check
# for POS + len(REF) - 1 (REF is e2+1 .. e3-1).
def pass_end(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: {CU.pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}) ->
  PEG(len, t, s, pos, e2, e3, lf):
  IF.bnd6(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, PEG(len, t, s, pos, e2, e3, lf), hok, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp),
    +b6 => +b67 => +b7 =>
      V.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, PEG(len, t, s, pos, e2, e3, lf), V.inv(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.hpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
        +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
          pass_end.k(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h20, h21, b6, b67, b7)))

# ---------------------------------------------------------------------------
# An INFO without END entry (the rewrite path's test) passes the check too
# ---------------------------------------------------------------------------

def ends_nil.k(+b: Bool, +p: String, +t: List<&2, String>, +hb: {b == False{} : Bool}, +ih: {B.Info.ends.go(t) == Nil{} : List<&2, Maybe<&2, Nat>>}) ->
  {B.Info.ends.put(b, p, B.Info.ends.go(t)) == Nil{} : List<&2, Maybe<&2, Nat>>}:
  %Equal.sym(Bool, b, False{}, hb) : {B.Info.ends.put(_, p, B.Info.ends.go(t)) == Nil{} : List<&2, Maybe<&2, Nat>>}
  ih

def ends_nil(+ps: List<&2, String>, +h: {B.Info.has.go(ps, "END") == False{} : Bool}) -> {B.Info.ends.go(ps) == Nil{} : List<&2, Maybe<&2, Nat>>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      +k = String.eq(B.Info.key(p), "END")
      ends_nil.k(k, p, t, Z.or_false_l(k, B.Info.has.go(t, "END"), h), ends_nil(t, Z.or_false_r(k, B.Info.has.go(t, "END"), h)))

# INFO, as J.pfs keeps it, passes the END check when the full split's INFO
# has no END entry.
def end_of_has(+body: String, +e: Nat, +h: {B.Info.has(B.Rec.field(B.Rec.fields(body), 7n), "END") == False{} : Bool}) ->
  {J.end_ok(B.Rec.field(J.pfs(body), 7n), e) == True{} : Bool}:
  +F = B.Rec.field(B.Rec.fields(body), 7n)
  +hn = ends_nil(String.split(F, ';'), h)
  Equal.trans(Bool, J.end_ok(B.Rec.field(J.pfs(body), 7n), e), J.end_ok(F, e), True{}, pfs_end(body, e),
    Equal.trans(Bool, J.end_ok(F, e), B.Info.end_ok(F, e), True{}, W.end_ok_eq(F, e),
      AB.subst(List<&2, Maybe<&2, Nat>>, z => {B.Info.end_ok.go(z, e) == True{} : Bool}, Nil{}, B.Info.ends(F), Equal.sym(List<&2, Maybe<&2, Nat>>, B.Info.ends(F), Nil{}, hn), {==})))

def has_end1(+x: String, r: {B.Info.has(x, "END") == False{} : Bool}
  & ({B.Info.has(x, "CIGAR") == False{} : Bool}
  & ({B.Info.has(x, "HOMLEN") == False{} : Bool}
  & ({B.Info.has(x, "HOMSEQ") == False{} : Bool}
  & {B.Info.has(x, "AA") == False{} : Bool})))) -> {B.Info.has(x, "END") == False{} : Bool}:
  match r:
    case (a, b):
      a
