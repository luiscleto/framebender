import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./tan.bend as V
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_window_defs.bend as WS
import ./proof_fast.bend as PF
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_cut.bend as CU
import ./proof_b_alleles.bend as AA
import ./proof_b_lines_str.bend as LSS
import ./proof_b_alleles_list.bend as AL
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_judge.bend as JG
import ./proof_b_adv_wr.bend as WR
import ./proof_b_lines.bend as LN
import ./proof_b_alleles_loop.bend as ALP
import lawful-bytes@0.1.0.0/proof_list.bend as BL
import ./proof_b_run.bend as PR
import ./proof_b_adv_ib.bend as IB
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_dec.bend as DE
import ./proof_b_budget_need.bend as BN
import ./proof_b_cut_str.bend as CS
import ./proof_b_cache_lem.bend as X
import ./proof_b_budget.bend as BG
import ./proof_b_budget_mb.bend as MB
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_bud_z4.bend as Z4
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The line the fast path handles, as WA sees it (proof_b_budget_need.bend's
# lfs, lchrom, lpos, lref, lgate on B.Text.line of the line's text): the
# cut's fields (proof_b_adv_hit.bend's hit_judge derives them the same way).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def X(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

def L1(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> B.Line:
  B.Text.line(P.btext(len, t, s, (lf - s : U32)))

def FS8(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32) -> List<&2, String>:
  [FH.FLD(len, t, n(s), n(e0)), FH.FLD(len, t, CU.nx(e0), n(e1)), FH.FLD(len, t, CU.nx(e1), n(e2)), FH.F3(len, t, e2, e3), FH.F4(len, t, e3, e4),
    FH.FLD(len, t, CU.nx(e4), n(e5)), FH.FLD(len, t, CU.nx(e5), n(e6)), ""]

# s <= lf: the line's LF is at or after its start.
def s_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) -> {Nat.is_le(n(s), n(lf)) == True{} : Bool}:
  +hfl = PJ.lf_first(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hjr = DE.j_range(len, t, d, s, lf, hok, hs, Equal.sym(Nat, D.first(X(len, t), n(s), n(len), 10), n(lf), hfl))
  W.and_l(Nat.is_le(n(s), n(lf)), Nat.is_le(n(lf), n(len)), hjr)

# The machine's fields of the line.
def lid_pfs(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {BN.lfs(L1(len, t, s, lf)) == FS8(len, t, s, e0, e1, e2, e3, e4, e5, e6) : List<&2, String>}:
  +Xs = X(len, t)
  +body = FH.BODY(len, t, s, lf)
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he3 = PJ.pa_3(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +f0 = FH.FLD(len, t, n(s), n(e0))
  +f1 = FH.FLD(len, t, CU.nx(e0), n(e1))
  +f2 = FH.FLD(len, t, CU.nx(e1), n(e2))
  +f5 = FH.FLD(len, t, CU.nx(e4), n(e5))
  +f6 = FH.FLD(len, t, CU.nx(e5), n(e6))
  +g3 = FH.F3(len, t, e2, e3)
  +g4 = FH.F4(len, t, e3, e4)
  +hpf = {%he2 : {J.pfs(body) == [f0, f1, f2, Norm.chars(D.slice(Xs, _, Nat.sub(n(e3), _))), g4, f5, f6, ""] : List<&2, String>};
    %he3 : {J.pfs(body) == [f0, f1, f2, FH.FLD(len, t, CU.nx(e2), n(e3)), Norm.chars(D.slice(Xs, _, Nat.sub(n(e4), _))), f5, f6, ""] : List<&2, String>};
    CU.pass_fields(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp) : {J.pfs(body) == [f0, f1, f2, g3, g4, f5, f6, ""] : List<&2, String>}}
  +A = P.btext(len, t, s, (lf - s : U32))
  +F = CU.fld(Xs, n(s), n(lf))
  +eA = FH.btext_fld(len, t, s, lf, s_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +eb = Equal.trans(String, B.Line.body(B.Text.line(A)), B.Line.body(B.Text.line(F)), body,
    Equal.cong(String, String, z => B.Line.body(B.Text.line(z)), A, F, eA),
    Equal.cong(B.Line, String, z => B.Line.body(z), B.Text.line(F), Norm.line(F), Equal.sym(B.Line, Norm.line(F), B.Text.line(F), LSS.line_eq(F))))
  Equal.trans(List<&2, String>, J.pfs(B.Line.body(B.Text.line(A))), J.pfs(body), [f0, f1, f2, g3, g4, f5, f6, ""],
    Equal.cong(String, List<&2, String>, z => J.pfs(z), B.Line.body(B.Text.line(A)), body, eb), hpf)

def LFT0(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) -> PJ.LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)

def lid_chrom(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {BN.lchrom(L1(len, t, s, lf)) == P.btext(len, t, s, (e0 - s : U32)) : String}:
  +hs0 = PJ.lf_s0(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +L = FS8(len, t, s, e0, e1, e2, e3, e4, e5, e6)
  Equal.trans(String, BN.lchrom(L1(len, t, s, lf)), B.Rec.field(L, 0n), P.btext(len, t, s, (e0 - s : U32)),
    Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 0n), BN.lfs(L1(len, t, s, lf)), L, lid_pfs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)),
    Equal.sym(String, P.btext(len, t, s, (e0 - s : U32)), FH.FLD(len, t, n(s), n(e0)), FH.btext_fld(len, t, s, e0, hs0)))

def lid_pos(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {BN.lpos(L1(len, t, s, lf)) == n(pos) : Nat}:
  +L = FS8(len, t, s, e0, e1, e2, e3, e4, e5, e6)
  Equal.trans(Nat, BN.lpos(L1(len, t, s, lf)), B.Rec.pos(L), n(pos),
    Equal.cong(List<&2, String>, Nat, z => B.Rec.pos(z), BN.lfs(L1(len, t, s, lf)), L, lid_pfs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)),
    Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), B.Pos.read(CU.fld(X(len, t), CU.nx(e0), n(e1))), Some{n(pos)},
      PJ.pp_read(len, t, pos, e0, e1, CU.pass_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))))

# e3 is inside the buffer.
def e3_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) -> {Nat.is_le(n(e4), n(len)) == True{} : Bool}:
  h = LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
  +hlx = PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h7l = PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h67 = PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h56 = PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h45 = PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, h)
  N.lt_to_le(n(e4), n(len), N.lt_trans(n(e4), n(e5), n(len), h45, N.lt_trans(n(e5), n(e6), n(len), h56, N.lt_trans(n(e6), n(e7), n(len), h67, N.le_lt_trans(n(e7), n(lf), n(len), h7l, hlx)))))

def lid_ref(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {BN.lref(L1(len, t, s, lf)) == n((e3 - e2 - 1 : U32)) : Nat}:
  +L = FS8(len, t, s, e0, e1, e2, e3, e4, e5, e6)
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34x = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +Xs = X(len, t)
  +a = n((e2 + 1 : U32))
  +b = n(e3)
  +hb = N.le_trans(b, n(len), List.length(&2, U32, Xs),
    N.le_trans(b, n(e4), n(len), N.lt_to_le(b, n(e4), h34x), e3_len(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)),
    %LP.len_x(len, t, d, hok) : {Nat.is_le(n(len), _) == True{} : Bool}; N.le_refl(n(len)))
  +el = Equal.trans(Nat, String.length(FH.F3(len, t, e2, e3)), List.length(&2, U32, D.slice(Xs, a, Nat.sub(b, a))), Nat.sub(b, a),
    CS.chars_len(D.slice(Xs, a, Nat.sub(b, a))), CS.slice_len(Xs, a, b, hb))
  Equal.trans(Nat, BN.lref(L1(len, t, s, lf)), String.length(FH.F3(len, t, e2, e3)), n((e3 - e2 - 1 : U32)),
    Equal.cong(List<&2, String>, Nat, z => String.length(B.Rec.field(z, 3n)), BN.lfs(L1(len, t, s, lf)), L, lid_pfs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)),
    Equal.trans(Nat, String.length(FH.F3(len, t, e2, e3)), Nat.sub(b, a), n((e3 - e2 - 1 : U32)), el,
      Equal.sym(Nat, n((e3 - e2 - 1 : U32)), Nat.sub(b, a), FH.n_rl(e2, e3, h23, he2))))

def or5(a0: Bool, a1: Bool, a2: Bool, a3: Bool, a4: Bool, +h0: {a0 == False{} : Bool}, +h1: {a1 == False{} : Bool}, +h2: {a2 == False{} : Bool},
  +h3: {a3 == False{} : Bool}, +h4: {a4 == False{} : Bool}) -> {Bool.or(Bool.or(Bool.or(Bool.or(a0, a1), a2), a3), a4) == False{} : Bool}:
  match a0 a1 a2 a3 a4:
    case False{} False{} False{} False{} False{}:
      {==}
    case True{} _ _ _ _:
      Empty.absurd({Bool.or(Bool.or(Bool.or(Bool.or(True{}, a1), a2), a3), a4) == False{} : Bool}, N.true_ne_false(h0))
    case False{} True{} _ _ _:
      Empty.absurd({Bool.or(Bool.or(Bool.or(Bool.or(False{}, True{}), a2), a3), a4) == False{} : Bool}, N.true_ne_false(h1))
    case False{} False{} True{} _ _:
      Empty.absurd({Bool.or(Bool.or(Bool.or(Bool.or(False{}, False{}), True{}), a3), a4) == False{} : Bool}, N.true_ne_false(h2))
    case False{} False{} False{} True{} _:
      Empty.absurd({Bool.or(Bool.or(Bool.or(Bool.or(False{}, False{}), False{}), True{}), a4) == False{} : Bool}, N.true_ne_false(h3))
    case False{} False{} False{} False{} True{}:
      Empty.absurd({Bool.or(Bool.or(Bool.or(Bool.or(False{}, False{}), False{}), False{}), True{}) == False{} : Bool}, N.true_ne_false(h4))

def lid_gate(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: FH.PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(s, e0) == True{} : Bool}) ->
  {BN.lgate(L1(len, t, s, lf)) == True{} : Bool}:
  +L = FS8(len, t, s, e0, e1, e2, e3, e4, e5, e6)
  +Xs = X(len, t)
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34x = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h01 = PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h12 = PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he3 = PJ.pa_3(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h4l = e3_len(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
  +h0l = N.lt_to_le(n(e0), n(len), N.lt_le_trans(n(e0), n(e4), n(len), N.lt_trans(n(e0), n(e1), n(e4), h01, N.lt_trans(n(e1), n(e2), n(e4), h12, N.lt_trans(n(e2), n(e3), n(e4), h23, h34x))), h4l))
  +h3 = {%he2 : {Nat.is_le(_, n(e3)) == True{} : Bool}; C.succ_le(n(e2), n(e3), h23) : {Nat.is_le(n((e2 + 1 : U32)), n(e3)) == True{} : Bool}}
  +h34 = {%he3 : {Nat.is_le(n(e3), _) == True{} : Bool}; N.le_add_r(n(e3), 1n) : {Nat.is_le(n(e3), n((e3 + 1 : U32))) == True{} : Bool}}
  +h4 = {%he3 : {Nat.is_le(_, n(e4)) == True{} : Bool}; C.succ_le(n(e3), n(e4), h34x) : {Nat.is_le(n((e3 + 1 : U32)), n(e4)) == True{} : Bool}}
  +hal = PJ.pa_al(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hs0 = PJ.lf_s0(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt0 = {%U.is_lt_to_nat(s, e0) : {_ == True{} : Bool}; hse : {Nat.is_lt(n(s), n(e0)) == True{} : Bool}}
  +h0 = FH.ne_chars(D.slice(Xs, n(s), Nat.sub(n(e0), n(s))),
    %Equal.sym(Nat, List.length(&2, U32, D.slice(Xs, n(s), Nat.sub(n(e0), n(s)))), Nat.sub(n(e0), n(s)), LP.slice_len(Xs, n(s), Nat.sub(n(e0), n(s)),
      %Equal.sym(Nat, Nat.add(n(s), Nat.sub(n(e0), n(s))), n(e0), N.le_sub_add(n(s), n(e0), hs0)) : {Nat.is_le(_, List.length(&2, U32, Xs)) == True{} : Bool};
      %LP.len_x(len, t, d, hok) : {Nat.is_le(n(e0), _) == True{} : Bool};
      h0l)) : {Nat.is_lt(0n, _) == True{} : Bool};
    LP.pos_sub(n(s), n(e0), hlt0))
  +hl = PJ.ap_l(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal))
  +he = PJ.ap_e(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal))
  +hr1 = Equal.cong(Maybe<&2, Nat>, Bool, m => Maybe.is_none(&2, Nat, m), B.Pos.read(CU.fld(Xs, CU.nx(e0), n(e1))), Some{n(pos)},
    PJ.pp_read(len, t, pos, e0, e1, CU.pass_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))
  +hl2 = Equal.cong(Bool, Bool, z => Bool.not(z), B.Text.is_letters(FH.F3(len, t, e2, e3)), True{}, hl)
  +hm = or5(Nat.is_lt(8n, 8n), String.is_empty(FH.FLD(len, t, n(s), n(e0))), Maybe.is_none(&2, Nat, B.Pos.read(CU.fld(Xs, CU.nx(e0), n(e1)))),
    Bool.not(B.Text.is_letters(FH.F3(len, t, e2, e3))), B.Text.any_empty(String.split(FH.F4(len, t, e3, e4), ',')), {==}, h0, hr1, hl2, he)
  Equal.trans(Bool, BN.lgate(L1(len, t, s, lf)), Bool.not(B.Rec.malformed(L)), True{},
    Equal.cong(List<&2, String>, Bool, z => Bool.not(B.Rec.malformed(z)), BN.lfs(L1(len, t, s, lf)), L, lid_pfs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)),
    Equal.cong(Bool, Bool, z => Bool.not(z), B.Rec.malformed(L), False{}, hm))

# (as proof_b_bud_vd.bend's cov_rs .. cov_reqof, pb-cache's)
# The Asks cover the line's windows.
def fc_rs(+rs: List<&2, Pr.Req>, +c: String, +a: Nat, +a2: Nat, +e: Nat, +e2: Nat,
  +h1: {X.hd1(rs, c, a) == True{} : Bool},
  +hl: {Norm.last_b(rs, 0n) == e : Nat},
  +ha: {Nat.is_le(a, a2) == True{} : Bool},
  +he: {Nat.is_le(e2, e) == True{} : Bool}) ->
  {BN.coversA(Some{rs}, c, a2, e2) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({BN.coversA(Some{Nil{}}, c, a2, e2) == True{} : Bool}, N.false_ne_true(h1))
    case Con{Pr.Req{+c1, +a1, +b1}, +t}:
      +ea = N.eq_sound(a1, a, W.and_r(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      W.and_tt(Bool.and(String.eq(c1, c), Nat.is_le(a1, a2)), Nat.is_le(e2, Norm.last_b(t, b1)),
        W.and_tt(String.eq(c1, c), Nat.is_le(a1, a2), W.and_l(String.eq(c1, c), Nat.is_eq(a1, a), h1),
          {%Equal.sym(Nat, a1, a, ea) : {Nat.is_le(_, a2) == True{} : Bool}; ha : {Nat.is_le(a1, a2) == True{} : Bool}}),
        {%Equal.sym(Nat, Norm.last_b(t, b1), e, hl) : {Nat.is_le(e2, _) == True{} : Bool}; he : {Nat.is_le(e2, Norm.last_b(t, b1)) == True{} : Bool}})

def fc_parts(+c: String, +a: Nat, +a2: Nat, +e: Nat, +e2: Nat, +ha: {Nat.is_le(a, a2) == True{} : Bool}, +he: {Nat.is_le(e2, e) == True{} : Bool}) ->
  {BN.coversA(Some{Norm.parts(c, a, e)}, c, a2, e2) == True{} : Bool}:
  +x = Nat.sub(e, a)
  fc_rs(Norm.parts(c, a, e), c, a, a2, e, e2, X.ph(x, Norm.le31(x), c, a, e), X.plast(x, Norm.le31(x), c, a, e, 0n), ha, he)

def fc_reqof.k(+one: Bool, +c: String, +a: Nat, +e: Nat, +a3: Nat, +ha: {Nat.is_le(a, a3) == True{} : Bool}) ->
  {BN.coversA(Some{Norm.Req.of.k(one, c, a, e, Nat.sub(a, Norm.margin()), Nat.max(e, Nat.add(a, Norm.ahead())))}, c, a3, e) == True{} : Bool}:
  match one:
    case True{}:
      +A2 = Nat.sub(a, Norm.margin())
      W.and_tt(Bool.and(String.eq(c, c), Nat.is_le(A2, a3)), Nat.is_le(e, Nat.max(e, Nat.add(a, Norm.ahead()))),
        W.and_tt(String.eq(c, c), Nat.is_le(A2, a3), X.str_eq_refl(c), N.le_trans(A2, a, a3, X.sub_le(a, Norm.margin()), ha)),
        X.le_max_l(e, Nat.add(a, Norm.ahead())))
    case False{}:
      fc_parts(c, a, a3, e, e, ha, N.le_refl(e))

def fc_reqof(+c: String, +a: Nat, +a3: Nat, +e: Nat, +ha: {Nat.is_le(a, a3) == True{} : Bool}) ->
  {BN.coversA(Some{Norm.Req.of(c, a, e)}, c, a3, e) == True{} : Bool}:
  fc_reqof.k(Norm.le31(Nat.sub(Nat.max(e, Nat.add(a, Norm.ahead())), Nat.sub(a, Norm.margin()))), c, a, e, a3, ha)


def RQF(+len: U32, +t: AT.Tree<U32>, +at: U32, +pos: U32, +e0: U32, +e2: U32, +e3: U32) -> List<&2, Pr.Req>:
  Norm.Req.of(P.btext(len, t, at, (e0 - at : U32)), Nat.sub(n(pos), 1n), Nat.add(Nat.sub(n(pos), 1n), n((e3 - e2 - 1 : U32))))

def wc.k(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool,
  +back: Nat, +wp: CD.WP,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hb0: {Nat.is_eq(back, 0n) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(FH.AofL(len, t, at, lf)) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(FH.AofL(len, t, at, lf)) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{}),
    Norm.Want{Norm.St{o, Norm.MB{Norm.retick(hold, P.mkRun(rp))}, Con{Norm.Src.of(hold, C.BT(len, t), at), P.mkSrcs(rest)}, P.mkPd(pd), eof, back, CD.mkWin(fa, wp), Some{RQF(len, t, at, pos, e0, e2, e3)}, True{}, dfs},
      RQF(len, t, at, pos, e0, e2, e3)}):
  match sl:
    case (+hsp, q):
      match q:
        case (+hn, q2):
          %Equal.sym(Norm.Src, Norm.Src.of(hold, C.BT(len, t), at), P.mkSrc(LI.SXP(hold, len, t, d, at)), HX.so_eq(hold, len, t, d, at)) :
            BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{}),
              Norm.Want{Norm.St{o, Norm.MB{Norm.retick(hold, P.mkRun(rp))}, Con{_, P.mkSrcs(rest)}, P.mkPd(pd), eof, back, CD.mkWin(fa, wp), Some{RQF(len, t, at, pos, e0, e2, e3)}, True{}, dfs}, RQF(len, t, at, pos, e0, e2, e3)})
          +chrom = P.btext(len, t, at, (e0 - at : U32))
          +p1 = Nat.sub(n(pos), 1n)
          +rl = n((e3 - e2 - 1 : U32))
          +e = Nat.add(p1, rl)
          +RQ = RQF(len, t, at, pos, e0, e2, e3)
          +L = L1(len, t, at, lf)
          +K = {1n+List.length(&2, Pr.Req, RQ) : Nat}
          +post = BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (lf + 1 : U32)}, rest}, pd, eof, back, wp, None{}, False{})
          +RR = BN.LAs(fa, MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs))
          +remB = BN.rem(fa, True{}, back, CD.mkWin(fa, wp), None{}, L)
          +remA = BN.rem(fa, False{}, back, CD.mkWin(fa, wp), Some{RQ}, L)
          +eB = MB.wa_split_h(hold, dfs, fa, cs, o, rp, len, t, d, at, lf, rest, pd, eof, back, wp, None{}, False{}, hsp, hn)
          +eA = MB.wa_split_h(hold, dfs, fa, cs, o, rp, len, t, d, at, lf, rest, pd, eof, back, wp, Some{RQ}, True{}, hsp, hn)
          +eR = Equal.sym(Nat, BN.lref(L), rl, lid_ref(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
          +ePos = lid_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
          +eP = Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), BN.lpos(L), n(pos), ePos)
          +eE = Equal.trans(Nat, BN.lend(L), Nat.add(p1, BN.lref(L)), e, Equal.cong(Nat, Nat, z => Nat.add(z, BN.lref(L)), BN.lp1(L), p1, eP),
            Equal.cong(Nat, Nat, z => Nat.add(p1, z), BN.lref(L), rl, Equal.sym(Nat, rl, BN.lref(L), eR)))
          +eC = lid_chrom(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
          +c0 = fc_reqof(chrom, p1, p1, e, N.le_refl(p1))
          +c1 = AB.subst(String, z => {BN.coversA(Some{RQ}, z, p1, e) == True{} : Bool}, chrom, BN.lchrom(L), Equal.sym(String, BN.lchrom(L), chrom, eC), c0)
          +c2 = AB.subst(Nat, z => {BN.coversA(Some{RQ}, BN.lchrom(L), z, e) == True{} : Bool}, p1, BN.lp1(L), Equal.sym(Nat, BN.lp1(L), p1, eP), c1)
          +hc = AB.subst(Nat, z => {BN.coversA(Some{RQ}, BN.lchrom(L), BN.lp1(L), z) == True{} : Bool}, e, BN.lend(L), Equal.sym(Nat, BN.lend(L), e, eE), c2)
          +hk0 = AB.subst(Nat, z => {Nat.is_le(List.length(&2, Pr.Req, RQ), BG.max1(z)) == True{} : Bool}, Nat.sub(e, p1), BN.lref(L),
            Equal.trans(Nat, Nat.sub(e, p1), rl, BN.lref(L), N.sub_add_l(p1, rl), eR), BG.reqof_len(chrom, p1, e))
          +kR = MB.want_rem(fa, back, wp, RQ, L, lid_gate(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp, hse), hc, hk0)
          +h1 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(remB, RR)) == True{} : Bool}, Nat.add(Nat.add(K, remA), RR), Nat.add(K, Nat.add(remA, RR)),
            N.add_assoc(K, remA, RR), N.le_add_mono_r(RR, Nat.add(K, remA), remB, kR))
          +hx = MB.wax_want(fa, o, K, False{}, back, wp, Some{RQ}, True{}, back, wp, None{}, L <> MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs), h1)
          +h2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(K, z), BN.WAX(fa, o, True{}, back, CD.mkWin(fa, wp), None{}, L <> MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs))) == True{} : Bool}, BN.WAX(fa, o, False{}, back, CD.mkWin(fa, wp), Some{RQ}, L <> MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs)), BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, Some{RQ}, True{})), cs), Equal.sym(Nat, BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, Some{RQ}, True{})), cs), BN.WAX(fa, o, False{}, back, CD.mkWin(fa, wp), Some{RQ}, L <> MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs)), eA), hx)
          (AB.subst(Nat, z => {Nat.is_le(Nat.add(K, BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, Some{RQ}, True{})), cs)), z) == True{} : Bool}, BN.WAX(fa, o, True{}, back, CD.mkWin(fa, wp), None{}, L <> MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs)), BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{})), cs), Equal.sym(Nat, BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{})), cs), BN.WAX(fa, o, True{}, back, CD.mkWin(fa, wp), None{}, L <> MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs)), eB), h2),
           MB.bi_b0(fa, back, wp, Some{RQ}, MB.AP(hold, len, t, d, at, rest, pd, eof, cs), hb0))

# The fast path's Want (fast.need with fneed False and back 0).
def want_c(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool,
  +back: Nat, +wp: CD.WP,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hb0: {Nat.is_eq(back, 0n) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{}),
    Norm.Want{Norm.St{o, Norm.MB{Norm.retick(hold, P.mkRun(rp))}, Con{Norm.Src.of(hold, C.BT(len, t), at), P.mkSrcs(rest)}, P.mkPd(pd), eof, back, CD.mkWin(fa, wp), Some{RQF(len, t, at, pos, e0, e2, e3)}, True{}, dfs},
      RQF(len, t, at, pos, e0, e2, e3)}):
  +hfl = PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt = PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  wc.k(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp, hse, hb0, LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt), hnr)

def kb.k(z: Bool, +back: Nat, +ez: {Nat.is_eq(back, 0n) == z : Bool}, y: Bool, +h: {Bool.or(z, y) == True{} : Bool}, hy: {y == True{} : Bool} -> Empty) ->
  {Nat.is_eq(back, 0n) == True{} : Bool}:
  match z:
    case True{}:
      ez
    case False{}:
      Empty.absurd({Nat.is_eq(back, 0n) == True{} : Bool}, hy(h))

def kb.s(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool,
  +back: Nat, +c: String, +a: Nat, +b: Nat, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hwp: {CD.wp_ok(fa, CD.WPKnown{c, a, b}) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +eqw: {Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(FH.AofL(len, t, at, lf)) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(FH.AofL(len, t, at, lf)) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  {Nat.is_eq(back, 0n) == True{} : Bool}:
  match sl:
    case (+hsp, q):
      match q:
        case (+hn, q2):
          +wp = {CD.WPKnown{c, a, b} : CD.WP}
          +L = L1(len, t, at, lf)
          +chrom = P.btext(len, t, at, (e0 - at : U32))
          +p1 = Nat.sub(n(pos), 1n)
          +rl = n((e3 - e2 - 1 : U32))
          +e = Nat.add(p1, rl)
          +pre = LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)
          +post = BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (lf + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed)
          +RL = MB.AP(hold, len, t, d, (lf + 1 : U32), rest, pd, eof, cs)
          +elh = MB.allx(hold, len, t, d, at, lf, rest, pd, eof, cs, hsp, hn)
          +h2 = AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, CD.mkWin(fa, wp), None{}, z) == True{} : Bool}, MB.AP(hold, len, t, d, at, rest, pd, eof, cs), L <> RL, elh, hbi)
          +ePos = lid_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
          +eP = Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), BN.lpos(L), n(pos), ePos)
          +eR = lid_ref(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
          +eE = Equal.trans(Nat, BN.lend(L), Nat.add(p1, BN.lref(L)), e, Equal.cong(Nat, Nat, z => Nat.add(z, BN.lref(L)), BN.lp1(L), p1, eP),
            Equal.cong(Nat, Nat, z => Nat.add(p1, z), BN.lref(L), rl, eR))
          +eC = lid_chrom(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
          kb.k(Nat.is_eq(back, 0n), back, {==}, BN.zheld(CD.mkWin(fa, wp), BN.lchrom(L), BN.lend(L)), h2,
            hz => N.true_ne_false(Equal.trans(Bool, True{}, BD.wo_need(Norm.against(CD.mkWin(fa, wp), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))), False{},
              Equal.sym(Bool, BD.wo_need(Norm.against(CD.mkWin(fa, wp), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))), True{},
                Equal.cong(Norm.Wo, Bool, z => BD.wo_need(z), Norm.against(CD.mkWin(fa, wp), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), Norm.WNeed{}}, eqw)),
              Z4.against_zero(fa, c, a, b, len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hb, hwp, hcl, hok, hs, hp, hse,
                AB.subst(Nat, z => {BN.zheld(CD.mkWin(fa, wp), chrom, z) == True{} : Bool}, BN.lend(L), e, eE,
                  AB.subst(String, z => {BN.zheld(CD.mkWin(fa, wp), z, BN.lend(L)) == True{} : Bool}, BN.lchrom(L), chrom, eC, hz))))))

# The fast path asks (against said WNeed with the window known) only when back
# is 0: else bi's zero window is held and fits, and against covers (Z4).
def kw_b0(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool,
  +back: Nat, +c: String, +a: Nat, +b: Nat, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hwp: {CD.wp_ok(fa, CD.WPKnown{c, a, b}) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +eqw: {Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  {Nat.is_eq(back, 0n) == True{} : Bool}:
  +hfl = PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt = PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, LFT0(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  kb.s(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, c, a, b, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hb, hwp, hcl, hok, hs, hp, hse, eqw, hbi,
    LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt), hnr)
