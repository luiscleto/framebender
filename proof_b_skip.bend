import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./proof_c_defs.bend as Q
import ./proof_b_cut.bend as CU
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_pos.bend as PO
import ./proof_b_skip_inv.bend as SI
import ./proof_b_skip_str.bend as SS
import ./proof_b_adv_proj.bend as PJ
import ./proof_c_pre_key.bend as K
import ./proof_b_alleles.bend as AL
import ./proof_fast.bend as PF
import ./proof_window.bend as PW
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# An out-of-scope line found on bytes (NF.line's Skip): its cut, POS and
# fields as for Pass (proof_b_cut.bend's lemmas, from the Skip inversion),
# and its verdict: the spec's judge gives Skipped, the line as it came,
# sorted by its POS (no reference read).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def SKIP(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Data:
  {CU.pre_of(len, t, s) == NF.Skip{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}

def shpre(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +hp: SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {M.PRE(len, t, s) == SI.S10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Pre}:
  Equal.trans(NF.Pre, M.PRE(len, t, s), CU.pre_of(len, t, s), SI.S10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf), Equal.sym(NF.Pre, CU.pre_of(len, t, s), M.PRE(len, t, s), CU.pre_eq(len, t, s)), hp)

def skip_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  SI.dsts(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf), SI.invs(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, shpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      CU.pass_lf.k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16))

def skip_pos(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  PO.PCT(len, t, CU.nx(e0), n(e1), pos):
  SI.dsts(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, PO.PCT(len, t, CU.nx(e0), n(e1), pos), SI.invs(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, shpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      CU.pass_pos.k(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18))

def skip_fields(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  CU.FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  SI.dsts(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.FDD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf), SI.invs(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, shpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      CU.pass_fields.k(len, t, d, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h21))

def skip_lt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {(U32.is_lt((e2 + 1 : U32), e3) && M.LETT(len, t, (e2 + 1 : U32), e3)) == True{} : Bool}:
  SI.dsts(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, {(U32.is_lt((e2 + 1 : U32), e3) && M.LETT(len, t, (e2 + 1 : U32), e3)) == True{} : Bool}, SI.invs(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, shpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      h19)

def skip_oos(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {M.OOS(len, t, (e3 + 1 : U32), e4) == True{} : Bool}:
  SI.dsts(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, {M.OOS(len, t, (e3 + 1 : U32), e4) == True{} : Bool}, SI.invs(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, shpre(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp)),
    +h0 => +h1 => +h2 => +h3 => +h4 => +h5 => +h6 => +h7 => +h8 => +h9 => +h10 => +h11 => +h12 => +h13 => +h14 => +h15 => +h16 => +h17 => +h18 => +h19 => +h20 => +h21 =>
      h20)

# ---------------------------------------------------------------------------
# The verdict
# ---------------------------------------------------------------------------

def RS(+p: Nat, +body: String) -> B.Res:
  B.Res{B.Skipped{}, p, body, False{}}

def BODY(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> String:
  CU.lbody(Q.xs(len, t), s, lf)

def FL(+len: U32, +t: AT.Tree<U32>, +a: Nat, +b: Nat) -> String:
  CU.fld(Q.xs(len, t), a, b)

def and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  N.and_true_l(a, b, h)

def and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  N.and_true_r(a, b, h)

def kh1(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, r: SS.KH(len, t, e, a, False{})) -> {B.Text.any_empty(SS.PS(len, t, e, a)) == False{} : Bool}:
  match r:
    case (x, y):
      x

def kh2(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, r: SS.KH(len, t, e, a, False{})) -> {B.Text.any_not_letters(SS.PS(len, t, e, a)) == True{} : Bool}:
  match r:
    case (x, y):
      y

# J.fast on these fields (no answer): Skipped.
def fast_skip(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +f7: String, +body: String, +p: Nat,
  +h0: {String.is_empty(f0) == False{} : Bool},
  +h1: {B.Pos.read(f1) == Some{p} : Maybe<&2, Nat>},
  +hl: {B.Text.is_letters(f3) == True{} : Bool},
  +he: {B.Text.any_empty(String.split(f4, ',')) == False{} : Bool},
  +hn: {B.Text.any_not_letters(String.split(f4, ',')) == True{} : Bool}) ->
  {J.fast(None{}, [f0, f1, f2, f3, f4, f5, f6, f7], body) == J.Other{Some{RS(B.Rec.pos([f0, f1, f2, f3, f4, f5, f6, f7]), body)}} : J.Fast}:
  +e1 = Equal.sym(Maybe<&2, Nat>, B.Pos.read(f1), Some{p}, h1)
  +FS = {[f0, f1, f2, f3, f4, f5, f6, f7] : List<&2, String>}
  +s4 = String.split(f4, ',')
  +G = {J.Other{Some{RS(B.Rec.pos(FS), body)}} : J.Fast}
  %Equal.sym(Bool, String.is_empty(f0), False{}, h0) :
    {J.fast.go(Bool.or(Bool.or(Bool.or(_, Bool.not(Maybe.is_some(&2, Nat, B.Pos.read(f1)))), Bool.not(B.Text.is_letters(f3))), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), None{}, FS, body) == G : J.Fast}
  %Equal.sym(Bool, B.Text.is_letters(f3), True{}, hl) :
    {J.fast.go(Bool.or(Bool.or(Bool.not(Maybe.is_some(&2, Nat, B.Pos.read(f1))), Bool.not(_)), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), None{}, FS, body) == G : J.Fast}
  %e1 :
    {J.fast.go(Bool.or(Bool.or(Bool.not(Maybe.is_some(&2, Nat, _)), False{}), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), None{}, FS, body) == G : J.Fast}
  %Equal.sym(Bool, B.Text.any_empty(s4), False{}, he) :
    {J.fast.go(_, B.Text.any_not_letters(s4), None{}, FS, body) == G : J.Fast}
  %Equal.sym(Bool, B.Text.any_not_letters(s4), True{}, hn) :
    {J.fast.go(False{}, _, None{}, FS, body) == G : J.Fast}
  {==}

# The spec's judge on an out-of-scope line found on bytes.
def skip_judge(+fa: List<&2, B.Contig>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(s, e0) == True{} : Bool}) ->
  {L.judge(fa, BODY(len, t, s, lf)) == RS(B.Rec.pos(B.Rec.fields(BODY(len, t, s, lf))), BODY(len, t, s, lf)) : B.Res}:
  +X = Q.xs(len, t)
  +body = BODY(len, t, s, lf)
  +h01 = PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h12 = PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34 = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h45 = PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h56 = PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h67 = PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h7l = PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlx = PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h4l = N.lt_to_le(n(e4), n(len), N.lt_trans(n(e4), n(e5), n(len), h45, N.lt_trans(n(e5), n(e6), n(len), h56, N.lt_trans(n(e6), n(e7), n(len), h67, N.le_lt_trans(n(e7), n(lf), n(len), h7l, hlx)))))
  +h3l = N.lt_to_le(n(e3), n(len), N.lt_le_trans(n(e3), n(e4), n(len), h34, h4l))
  +h2l = N.lt_trans(n(e2), n(e3), n(len), h23, N.lt_le_trans(n(e3), n(e4), n(len), h34, h4l))
  +h0l = N.lt_to_le(n(e0), n(len), N.lt_trans(n(e0), n(e1), n(len), h01, N.lt_trans(n(e1), n(e2), n(len), h12, h2l)))
  +i2 = CU.inc(len, t, d, e2, hok, h2l)
  +i3 = CU.inc(len, t, d, e3, hok, N.lt_le_trans(n(e3), n(e4), n(len), h34, h4l))
  +f0 = FL(len, t, n(s), n(e0))
  +f1 = FL(len, t, CU.nx(e0), n(e1))
  +f2 = FL(len, t, CU.nx(e1), n(e2))
  +f3 = FL(len, t, CU.nx(e2), n(e3))
  +f4 = FL(len, t, CU.nx(e3), n(e4))
  +f5 = FL(len, t, CU.nx(e4), n(e5))
  +f6 = FL(len, t, CU.nx(e5), n(e6))
  +F7P = B.Rec.field(J.pfs(body), 7n)
  +FS = {[f0, f1, f2, f3, f4, f5, f6, F7P] : List<&2, String>}
  +hpf = {skip_fields(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp) : {J.pfs(body) == FS : List<&2, String>}}
  +hlt0 = Equal.trans(Bool, Nat.is_lt(n(s), n(e0)), U32.is_lt(s, e0), True{}, Equal.sym(Bool, U32.is_lt(s, e0), Nat.is_lt(n(s), n(e0)), U.is_lt_to_nat(s, e0)), hse)
  +h0 = SS.ne_fld(len, t, d, s, e0, hok, hlt0, h0l)
  +h1 = PJ.pp_read(len, t, pos, e0, e1, skip_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt = skip_lt(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
  +hlt3 = Equal.trans(Bool, Nat.is_lt(n((e2 + 1 : U32)), n(e3)), U32.is_lt((e2 + 1 : U32), e3), True{}, Equal.sym(Bool, U32.is_lt((e2 + 1 : U32), e3), Nat.is_lt(n((e2 + 1 : U32)), n(e3)), U.is_lt_to_nat((e2 + 1 : U32), e3)),
    and_l(U32.is_lt((e2 + 1 : U32), e3), M.LETT(len, t, (e2 + 1 : U32), e3), hlt))
  +hl = AB.subst(Nat, z => {B.Text.is_letters(Q.fld(X, z, n(e3))) == True{} : Bool}, n((e2 + 1 : U32)), CU.nx(e2), Equal.sym(Nat, CU.nx(e2), n((e2 + 1 : U32)), i2),
    Equal.trans(Bool, B.Text.is_letters(Q.fld(X, n((e2 + 1 : U32)), n(e3))), M.LETT(len, t, (e2 + 1 : U32), e3), True{}, SS.lett_s(len, t, d, (e2 + 1 : U32), e3, hok, hlt3, h3l),
      and_r(U32.is_lt((e2 + 1 : U32), e3), M.LETT(len, t, (e2 + 1 : U32), e3), hlt)))
  +h34b = AB.subst(Nat, z => {Nat.is_le(z, n(e4)) == True{} : Bool}, CU.nx(e3), n((e3 + 1 : U32)), i3, C.succ_le(n(e3), n(e4), h34))
  +ys = D.slice(X, CU.nx(e3), Nat.sub(n(e4), CU.nx(e3)))
  +sp = Equal.trans(List<&2, String>, String.split(f4, ','), AL.mapc(FD.split(ys, 44)), SS.PS(len, t, e4, (e3 + 1 : U32)),
    K.csplit_g(ys, 44),
    Equal.cong(Nat, List<&2, String>, z => AL.mapc(FD.split(D.slice(X, z, Nat.sub(n(e4), z)), 44)), CU.nx(e3), n((e3 + 1 : U32)), i3))
  +he = AB.subst(List<&2, String>, z => {B.Text.any_empty(z) == False{} : Bool}, SS.PS(len, t, e4, (e3 + 1 : U32)), String.split(f4, ','), Equal.sym(List<&2, String>, String.split(f4, ','), SS.PS(len, t, e4, (e3 + 1 : U32)), sp), kh1(len, t, e4, (e3 + 1 : U32), SS.oos_v(len, t, d, (e3 + 1 : U32), e4, hok, h4l, h34b, skip_oos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))))
  +hn = AB.subst(List<&2, String>, z => {B.Text.any_not_letters(z) == True{} : Bool}, SS.PS(len, t, e4, (e3 + 1 : U32)), String.split(f4, ','), Equal.sym(List<&2, String>, String.split(f4, ','), SS.PS(len, t, e4, (e3 + 1 : U32)), sp), kh2(len, t, e4, (e3 + 1 : U32), SS.oos_v(len, t, d, (e3 + 1 : U32), e4, hok, h4l, h34b, skip_oos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))))
  +P0 = B.Rec.pos(B.Rec.fields(body))
  +ep = Equal.trans(Nat, B.Rec.pos(FS), B.Rec.pos(J.pfs(body)), P0,
    Equal.cong(List<&2, String>, Nat, z => B.Rec.pos(z), FS, J.pfs(body), Equal.sym(List<&2, String>, J.pfs(body), FS, hpf)), PF.pfs_pos(body))
  +es = {%Equal.sym(List<&2, String>, J.pfs(body), FS, hpf) : {J.fast(None{}, _, body) == J.Other{Some{RS(P0, body)}} : J.Fast};
    %ep : {J.fast(None{}, FS, body) == J.Other{Some{RS(_, body)}} : J.Fast};
    fast_skip(f0, f1, f2, f3, f4, f5, f6, F7P, body, n(pos), h0, h1, hl, he, hn) : {J.fast(None{}, J.pfs(body), body) == J.Other{Some{RS(P0, body)}} : J.Fast}}
  +ej = Equal.trans(Maybe<&2, B.Res>, J.judge_in(None{}, body), PF.fr_res(J.fast(None{}, J.pfs(body), body), P0, body), Some{RS(P0, body)},
    Equal.sym(Maybe<&2, B.Res>, PF.fr_res(J.fast(None{}, J.pfs(body), body), P0, body), J.judge_in(None{}, body), PF.fast_judge(None{}, body)),
    Equal.cong(J.Fast, Maybe<&2, B.Res>, f => PF.fr_res(f, P0, body), J.fast(None{}, J.pfs(body), body), J.Other{Some{RS(P0, body)}}, es))
  Equal.sym(B.Res, RS(P0, body), L.judge(fa, body), PW.window(fa, body, None{}, RS(P0, body), {==}, ej))
