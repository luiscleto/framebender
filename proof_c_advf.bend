import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_cut.bend as CU
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_nat.bend as LP
import ./proof_b_cache.bend as CA
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_cache_lem.bend as X
import ./proof_window_lists.bend as WL
import ./proof_b_lit.bend as LT
import ./proof_b_lines_pd.bend as Y
import ./proof_b_lines_str.bend as LSS
import ../lawful-words/proof_nat.bend as NN
import ../lawful-bytes/bytes.bend as BY
import ./proof_c_defs.bend as Q
import ./proof_c_pre.bend as PE
import ./proof_c_cache.bend as CC
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Phase C: facts of a line that passed NX.line's tests, from
# proof_c_pre.bend's deliverables, in the forms proof_c_adv.bend and
# proof_c_hit.bend use. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# The line passed NX.line's tests with this cut and these alleles.
def FXP(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool) -> Data:
  {Q.fx_of(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}

# ---------------------------------------------------------------------------
# Facts of a passed line (proof_c_pre.bend's deliverables)
# ---------------------------------------------------------------------------

def lfd(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  PE.fix_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)

# ALT's end, then CHROM's end, are inside the buffer.
def e4le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(n(e4), n(len)) == True{} : Bool}:
  N.lt_to_le(n(e4), n(len), N.lt_trans(n(e4), n(e5), n(len), PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(n(e5), n(e6), n(len), PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(n(e6), n(e7), n(len), PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.le_lt_trans(n(e7), n(lf), n(len), PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))))))

def e0le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(n(e0), n(len)) == True{} : Bool}:
  N.lt_to_le(n(e0), n(len), N.lt_le_trans(n(e0), n(e4), n(len), N.lt_trans(n(e0), n(e1), n(e4), PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(n(e1), n(e2), n(e4), PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(n(e2), n(e3), n(e4), PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))), e4le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

def POSF(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32) -> Type:
  {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}
  & ({Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}
  & {U32.is_lt(pos, 1000000000) == True{} : Bool}))

def pf.nz(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, h: POSF(len, t, pos, e0, e1)) -> {Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}:
  (a1, r1) = h
  (a2, r2) = r1
  (a3, a4) = r2
  a3

def pf.small(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, h: POSF(len, t, pos, e0, e1)) -> {U32.is_lt(pos, 1000000000) == True{} : Bool}:
  (a1, r1) = h
  (a2, r2) = r1
  (a3, a4) = r2
  a4

def posnz(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_eq(n(pos), 0n) == False{} : Bool}:
  pf.nz(len, t, pos, e0, e1, PE.fix_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))

def possmall(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {U32.is_lt(pos, 1000000000) == True{} : Bool}:
  pf.small(len, t, pos, e0, e1, PE.fix_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))

# The alleles' facts with REF first.
def ALSF(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +lf: U32, +als: List<&2, NX.Ap>) -> Type:
  {Q.ALS_IN(lf, PE.REF(e2, e3) <> Q.TL(als)) == True{} : Bool} & {Q.ALS_L(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als)) == True{} : Bool}

def alsf.k(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  h: {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), PE.REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))) -> ALSF(len, t, e2, e3, lf, als):
  (+eq, r1) = h
  (sp, r2) = r1
  (hin, r3) = r2
  (hl, r4) = r3
  (AB.subst(List<&2, NX.Ap>, z => {Q.ALS_IN(lf, z) == True{} : Bool}, als, PE.REF(e2, e3) <> Q.TL(als), eq, hin),
   AB.subst(List<&2, NX.Ap>, z => {Q.ALS_L(Q.xs(len, t), z) == True{} : Bool}, als, PE.REF(e2, e3) <> Q.TL(als), eq, hl))

def alsf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) -> ALSF(len, t, e2, e3, lf, als):
  alsf.k(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))

def af.in(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +lf: U32, +als: List<&2, NX.Ap>, h: ALSF(len, t, e2, e3, lf, als)) -> {Q.ALS_IN(lf, PE.REF(e2, e3) <> Q.TL(als)) == True{} : Bool}:
  (a, b) = h
  a

def af.l(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +lf: U32, +als: List<&2, NX.Ap>, h: ALSF(len, t, e2, e3, lf, als)) -> {Q.ALS_L(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als)) == True{} : Bool}:
  (a, b) = h
  b

def RL(+e2: U32, +e3: U32) -> U32:
  (e3 - (e2 + 1 : U32) : U32)

# REF: one byte or more, inside the line, letters.
def rlpos(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {U32.is_lt(0, RL(e2, e3)) == True{} : Bool}:
  +h1 = N.and_true_l(Nat.is_le(1n, n(RL(e2, e3))), Nat.is_le(Nat.add(n((e2 + 1 : U32)), n(RL(e2, e3))), n(lf)), N.and_true_l(Bool.and(Nat.is_le(1n, n(RL(e2, e3))), Nat.is_le(Nat.add(n((e2 + 1 : U32)), n(RL(e2, e3))), n(lf))), Q.ALS_IN(lf, Q.TL(als)), af.in(len, t, e2, e3, lf, als, alsf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))
  %Equal.sym(Bool, U32.is_lt(0, RL(e2, e3)), Nat.is_lt(n(0), n(RL(e2, e3))), U.is_lt_to_nat(0, RL(e2, e3))) : {_ == True{} : Bool}
  %N.le_succ_lt(0n, n(RL(e2, e3))) : {_ == True{} : Bool}
  h1

def reffit(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(Nat.add(n((e2 + 1 : U32)), n(RL(e2, e3))), n(len)) == True{} : Bool}:
  +h1 = N.and_true_r(Nat.is_le(1n, n(RL(e2, e3))), Nat.is_le(Nat.add(n((e2 + 1 : U32)), n(RL(e2, e3))), n(lf)), N.and_true_l(Bool.and(Nat.is_le(1n, n(RL(e2, e3))), Nat.is_le(Nat.add(n((e2 + 1 : U32)), n(RL(e2, e3))), n(lf))), Q.ALS_IN(lf, Q.TL(als)), af.in(len, t, e2, e3, lf, als, alsf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))
  N.le_trans(Nat.add(n((e2 + 1 : U32)), n(RL(e2, e3))), n(lf), n(len), h1, N.lt_to_le(n(lf), n(len), PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))

def reflets(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Q.lets(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(RL(e2, e3)))) == True{} : Bool}:
  N.and_true_l(Q.lets(Q.SL(Q.xs(len, t), PE.REF(e2, e3))), Q.ALS_L(Q.xs(len, t), Q.TL(als)), af.l(len, t, e2, e3, lf, als, alsf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

