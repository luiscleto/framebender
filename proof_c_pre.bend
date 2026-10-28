import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./norm_line.bend as J
import ./proof_c_defs.bend as Q
import ./proof_b_cut.bend as CU
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_b_cut_nat.bend as Z
import ./proof_b_cut_fx.bend as FX
import ./proof_b_cut_pos.bend as PO
import ../lawful-fields/proof_num.bend as LN
import ./proof_c_pre_pair.bend as P
import ./proof_c_pre_inv.bend as I
import ./proof_c_pre_cut.bend as K
import ./proof_c_pre_let.bend as L
import ./proof_c_pre_als.bend as AS
import ./proof_c_pre_ifo.bend as IF
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# Phase C, area "pre": the rewrite path's tests on a line's bytes
# (norm_fix.bend's NX.line) against the String path, as proof_b_cut.bend
# does for the fast path's NF.line. When a line passes: its cut is the
# String path's fields, POS reads as written, the alleles are letters read
# as Q.BF reads them, distinct, and INFO has no entry with the keys judging
# and rewriting look at. Notes: notes/rewrite_pre.md.
#
# Notation: the buffer is C.BT(len, t), Q.xs its view, Q.n(x) U32.to_nat(x),
# Q.fld(ys, a, b) the text of bytes a .. b-1, Q.nx(e) = n(e) + 1.

def REF(+e2: U32, +e3: U32) -> NX.Ap:
  NX.Ap{(e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)}

# Field 7 (INFO) of the line's fields as B.Rec.fields splits its body.
def F7(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> String:
  B.Rec.field(B.Rec.fields(CU.lbody(Q.xs(len, t), s, lf)), 7n)

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# NX.line hands the buffer back unchanged.
def line_pair(+len: U32, +t: AT.Tree<U32>, +s: U32) ->
  {NX.line(C.BT(len, t), s) == NX.Fr{C.BT(len, t), Q.fx_of(len, t, s)} : NX.Fr}:
  %Equal.sym(NX.Fr, NX.line(C.BT(len, t), s), NX.Fr{C.BT(len, t), P.FX(len, t, s)}, P.line_t(len, t, s)) :
    {_ == NX.Fr{C.BT(len, t), Q.Fr.p(_)} : NX.Fr}
  {==}

# The line's LF is the first LF at or after s, inside the buffer, and the
# field ends are in order (as proof_b_cut.bend's pass_lf).
def fix_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +als: List<&2, NX.Ap>, +up: Bool,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  I.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf), K.invx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => htt =>
      CU.pass_lf.k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16))

# The String path cuts the same fields, INFO kept as "" (as pass_fields).
def fix_fields(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +als: List<&2, NX.Ap>, +up: Bool,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  CU.FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  I.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, CU.FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf), K.invx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => htt =>
      I.dtt(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, CU.FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf), htt,
        +g1 => +g2 => +g3 => +g4 => +g5 => +g6 => +g7 => +g8 => +g9 => +g10 =>
          CU.pass_fields.k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, g8, g10)))

# POS reads as the number read, written as Nat.show writes it, not 0, and
# below 10^9 (as pass_pos and pass_pos_small).
def fix_pos(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +als: List<&2, NX.Ap>, +up: Bool,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}
  & ({Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}
  & {U32.is_lt(pos, 1000000000) == True{} : Bool})):
  I.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, K.POS4(len, t, e0, e1, pos), K.invx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => htt =>
      I.dtt(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, K.POS4(len, t, e0, e1, pos), htt,
        +g1 => +g2 => +g3 => +g4 => +g5 => +g6 => +g7 => +g8 => +g9 => +g10 =>
          K.pos4(len, t, e0, e1, pos, CU.pass_pos.k(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, g1, g2),
            PO.pos_small(len, t, (e0 + 1 : U32), e1, pos, Nat.pow(2n, 32n), U32.to_nat(429496729), {==}, {==}, LN.QM(Nat.pow(2n, 32n), {==}), g1, g2))))

# The alleles: REF, then the ALT field cut at its commas; each one or more
# letters A, C, G, T, N (either case) inside the line; distinct as bases;
# up says REF and ALT are written as B.Rec.rebuild writes them.
def fix_als(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +als: List<&2, NX.Ap>, +up: Bool,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  {als == REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool})))):
  +hok2 = Equal.sym(Bool, True{}, D.ok(C.BT(len, t), d), Equal.sym(Bool, D.ok(C.BT(len, t), d), True{}, hok))
  +hs2 = Equal.sym(Bool, True{}, U32.is_le(s, len), Equal.sym(Bool, U32.is_le(s, len), True{}, hs))
  +hp2 = Equal.sym(NX.Fp, NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up}, Q.fx_of(len, t, s), Equal.sym(NX.Fp, Q.fx_of(len, t, s), NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up}, hp))
  K.bnd(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AS.G6(len, t, e2, e3, e4, lf, als, up), fix_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok2, hs2, hp2),
    +b2 => +b3 => +b4l => +bll =>
      I.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, AS.G6(len, t, e2, e3, e4, lf, als, up), K.invx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp2),
        +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => htt =>
          I.dtt(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, AS.G6(len, t, e2, e3, e4, lf, als, up), htt,
            +g1 => +g2 => +g3 => +g4 => +g5 => +g6 => +g7 => +g8 => +g9 => +g10 =>
              AS.als_core(len, t, d, e2, e3, e4, lf, als, up, hok2, b2, b3, b4l, bll, g3, g4, g5, g6, g7))))

# Letters A, C, G, T, N in either case read as their bases.
def read_bf(+ys: List<&2, U32>, hl: {Q.lets(ys) == True{} : Bool}) ->
  {B.Allele.read(Norm.chars(ys)) == Some{Q.BF(ys)} : Maybe<&2, List<&2, B.Base>>}:
  L.read_bf(ys, hl)

# INFO, as the String path's full field split has it (B.Rec.rebuild and
# B.Rec.stale read it there), has no entry with key END, CIGAR, HOMLEN,
# HOMSEQ or AA.
def fix_info(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +als: List<&2, NX.Ap>, +up: Bool,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  {B.Info.has(F7(len, t, s, lf), "END") == False{} : Bool}
  & ({B.Info.has(F7(len, t, s, lf), "CIGAR") == False{} : Bool}
  & ({B.Info.has(F7(len, t, s, lf), "HOMLEN") == False{} : Bool}
  & ({B.Info.has(F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}
  & {B.Info.has(F7(len, t, s, lf), "AA") == False{} : Bool}))):
  +hok2 = Equal.sym(Bool, True{}, D.ok(C.BT(len, t), d), Equal.sym(Bool, D.ok(C.BT(len, t), d), True{}, hok))
  +hs2 = Equal.sym(Bool, True{}, U32.is_le(s, len), Equal.sym(Bool, U32.is_le(s, len), True{}, hs))
  +hp2 = Equal.sym(NX.Fp, NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up}, Q.fx_of(len, t, s), Equal.sym(NX.Fp, Q.fx_of(len, t, s), NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up}, hp))
  IF.bnd6(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, IF.NOK(len, t, s, lf), hok2, fix_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok2, hs2, hp2),
    +b6 => +b67 => +b7 =>
      I.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, IF.NOK(len, t, s, lf), K.invx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp2),
        +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => htt =>
          I.dtt(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, IF.NOK(len, t, s, lf), htt,
            +g1 => +g2 => +g3 => +g4 => +g5 => +g6 => +g7 => +g8 => +g9 => +g10 =>
              IF.info_fin(len, t, d, s, e6, e7, lf, hok2, b6, b67, b7, g9,
                IF.info_k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok2, hs2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, g8, g10)))))

# The ends of CHROM .. ALT are tabs.
def fix_tabs(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +als: List<&2, NX.Ap>, +up: Bool,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  {List.get(&2, U32, Q.xs(len, t), Q.n(e0)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e1)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e2)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e3)) == Some{9} : Maybe<&2, U32>}
  & {List.get(&2, U32, Q.xs(len, t), Q.n(e4)) == Some{9} : Maybe<&2, U32>}))):
  +hok2 = Equal.sym(Bool, True{}, D.ok(C.BT(len, t), d), Equal.sym(Bool, D.ok(C.BT(len, t), d), True{}, hok))
  +hs2 = Equal.sym(Bool, True{}, U32.is_le(s, len), Equal.sym(Bool, U32.is_le(s, len), True{}, hs))
  I.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, K.TAB(len, t, e0) & (K.TAB(len, t, e1) & (K.TAB(len, t, e2) & (K.TAB(len, t, e3) & K.TAB(len, t, e4)))), K.invx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => htt =>
      (K.tab_e(len, t, M.E0(len, t, s), e0, Equal.cong(NF.Cut, U32, c => CU.ce0(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h15),
        Z.tabget(len, t, d, M.E0(len, t, s), 9, hok2, FX.ltE0(len, t, d, s, hok2, hs2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14), h1)),
      (K.tab_e(len, t, M.E1(len, t, s), e1, Equal.cong(NF.Cut, U32, c => CU.ce1(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h15),
        Z.tabget(len, t, d, M.E1(len, t, s), 9, hok2, FX.ltE1(len, t, d, s, hok2, hs2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14), h3)),
      (K.tab_e(len, t, M.E2(len, t, s), e2, Equal.cong(NF.Cut, U32, c => CU.ce2(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h15),
        Z.tabget(len, t, d, M.E2(len, t, s), 9, hok2, FX.ltE2(len, t, d, s, hok2, hs2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14), h5)),
      (K.tab_e(len, t, M.E3(len, t, s), e3, Equal.cong(NF.Cut, U32, c => CU.ce3(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h15),
        Z.tabget(len, t, d, M.E3(len, t, s), 9, hok2, FX.ltE3(len, t, d, s, hok2, hs2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14), h7)),
      K.tab_e(len, t, M.E4(len, t, s), e4, Equal.cong(NF.Cut, U32, c => CU.ce4(c), V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))), V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h15),
        Z.tabget(len, t, d, M.E4(len, t, s), 9, hok2, FX.ltE4(len, t, d, s, hok2, hs2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14), h9)))))))

# When INFO is the last field, the line does not end in CR.
def fix_cr(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +als: List<&2, NX.Ap>, +up: Bool,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool},
  hp: {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  {(U32.is_eq(e7, lf) && U32.is_eq(C.AT(len, t, (lf - 1 : U32)), 13)) == False{} : Bool}:
  I.dst(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, {(U32.is_eq(e7, lf) && U32.is_eq(C.AT(len, t, (lf - 1 : U32)), 13)) == False{} : Bool}, K.invx(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => htt =>
      I.dtt(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, {(U32.is_eq(e7, lf) && U32.is_eq(C.AT(len, t, (lf - 1 : U32)), 13)) == False{} : Bool}, htt,
        +g1 => +g2 => +g3 => +g4 => +g5 => +g6 => +g7 => +g8 => +g9 => +g10 =>
          FX.not_true(U32.is_eq(e7, lf) && U32.is_eq(C.AT(len, t, (lf - 1 : U32)), 13), g10)))
