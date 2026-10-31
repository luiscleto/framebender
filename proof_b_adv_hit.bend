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
import ./proof_b_mw.bend as MW
import ./proof_s_multi.bend as MU
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The fast path's hit (norm.bend's fast.hit), its verdict: a line that
# passes NF.line, whose CHROM is the window's contig and whose REF check
# passes on the window's letters, is judged by the spec as it is. Every
# variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

def BODY(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> String:
  CU.lbody(xs(len, t), s, lf)

def PASS(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Data:
  {CU.pre_of(len, t, s) == NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Pre}

# The first LF from at is at or after at, and inside the buffer.
law j_range:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +j: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {U32.is_le(at, len) == True{} : Bool}
  for +hjf: {n(j) == D.first(xs(len, t), n(at), n(len), 10) : Nat}
  {Bool.and(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len))) == True{} : Bool}

def j_range(len, t, d, at, j, hok, hs, hjf):
  %Equal.sym(Nat, n(j), D.first(xs(len, t), n(at), n(len), 10), hjf) : {Bool.and(Nat.is_le(n(at), _), Nat.is_le(_, n(len))) == True{} : Bool}
  BL.first_range(xs(len, t), n(at), n(len), 10, LI.u2n(at, len, hs), %LP.len_x(len, t, d, hok) : {Nat.is_le(n(len), _) == True{} : Bool}; N.le_refl(n(len)))

# Small facts
# ===========

law ne_chars:
  for +ys: List<&2, U32>
  for +h: {Nat.is_lt(0n, List.length(&2, U32, ys)) == True{} : Bool}
  {String.is_empty(Norm.chars(ys)) == False{} : Bool}

def ne_chars(ys, h):
  match ys:
    case Nil{}:
      Empty.absurd({String.is_empty(Norm.chars(Nil{})) == False{} : Bool}, W.ft(h))
    case Con{+y, +r}:
      {==}

law bo_eq:
  for +ys: List<&2, U32>
  {CD.bases_of(ys) == AA.bases_of(ys) : List<&2, B.Base>}

def bo_eq(ys):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %bo_eq(r) : {CD.lb(y) <> CD.bases_of(r) == AA.lb(y) <> _ : List<&2, B.Base>}
      {==}

law up_eq:
  for +ys: List<&2, U32>
  {AA.up(ys) == CD.up(ys) : Bool}

def up_eq(ys):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %up_eq(r) : {Bool.and(NF.is_base(y), AA.up(r)) == Bool.and(NF.is_base(y), _) : Bool}
      {==}

# The text of bytes a .. b-1, two ways.
law btext_fld:
  for +len: U32
  for +t: AT.Tree<U32>
  for +a: U32
  for +b: U32
  for +hab: {Nat.is_le(n(a), n(b)) == True{} : Bool}
  {P.btext(len, t, a, (b - a : U32)) == CU.fld(xs(len, t), n(a), n(b)) : String}

def btext_fld(len, t, a, b, hab):
  %Equal.sym(Nat, n((b - a : U32)), Nat.sub(n(b), n(a)), LP.sub_u(b, a, hab)) : {NR.chars(D.slice(xs(len, t), n(a), _)) == CU.fld(xs(len, t), n(a), n(b)) : String}
  Equal.sym(String, Norm.chars(D.slice(xs(len, t), n(a), Nat.sub(n(b), n(a)))), NR.chars(D.slice(xs(len, t), n(a), Nat.sub(n(b), n(a)))), LSS.chars_norm(D.slice(xs(len, t), n(a), Nat.sub(n(b), n(a)))))

# REF's length as the fast path computes it.
law n_rl:
  for +e2: U32
  for +e3: U32
  for +hlt: {Nat.is_lt(n(e2), n(e3)) == True{} : Bool}
  for +hinc: {Nat.add(n(e2), 1n) == n((e2 + 1 : U32)) : Nat}
  {n((e3 - e2 - 1 : U32)) == Nat.sub(n(e3), n((e2 + 1 : U32))) : Nat}

def n_rl(e2, e3, hlt, hinc):
  +hle = N.lt_to_le(n(e2), n(e3), hlt)
  +x = Nat.sub(n(e3), Nat.add(n(e2), 1n))
  +h1 = {%Equal.sym(Nat, n((e3 - e2 : U32)), Nat.sub(n(e3), n(e2)), LP.sub_u(e3, e2, hle)) : {Nat.is_le(1n, _) == True{} : Bool};
    %Equal.sym(Nat, Nat.sub(n(e3), n(e2)), 1n+x, AL.sub_lt(n(e3), n(e2), hlt)) : {Nat.is_le(1n, _) == True{} : Bool};
    N.le_zero_l(x) : {Nat.is_le(1n, n((e3 - e2 : U32))) == True{} : Bool}}
  %Equal.sym(Nat, n((e3 - e2 - 1 : U32)), Nat.sub(n((e3 - e2 : U32)), n(1)), LP.sub_u((e3 - e2 : U32), 1, h1)) : {_ == Nat.sub(n(e3), n((e2 + 1 : U32))) : Nat}
  %Equal.sym(Nat, n((e3 - e2 : U32)), Nat.sub(n(e3), n(e2)), LP.sub_u(e3, e2, hle)) : {Nat.sub(_, 1n) == Nat.sub(n(e3), n((e2 + 1 : U32))) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.sub(n(e3), n(e2)), 1n), x, AL.sub_sub(n(e3), n(e2), 1n)) : {_ == Nat.sub(n(e3), n((e2 + 1 : U32))) : Nat}
  %hinc : {x == Nat.sub(n(e3), _) : Nat}
  {==}

# The verdict
# ===========

def F3(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32) -> String:
  Norm.chars(AA.sl(xs(len, t), (e2 + 1 : U32), e3))

def F4(+len: U32, +t: AT.Tree<U32>, +e3: U32, +e4: U32) -> String:
  Norm.chars(AA.sl(xs(len, t), (e3 + 1 : U32), e4))

def FLD(+len: U32, +t: AT.Tree<U32>, +a: Nat, +b: Nat) -> String:
  CU.fld(xs(len, t), a, b)

def hit_judge(+fa: List<&2, B.Contig>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(s, e0) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, s, (e0 - s : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(n(pos), 1n), CD.bases_of(D.slice(xs(len, t), n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool}) ->
  {L.judge(fa, BODY(len, t, s, lf)) == JG.RN(B.Rec.pos(B.Rec.fields(BODY(len, t, s, lf))), BODY(len, t, s, lf)) : B.Res}:
  +X = xs(len, t)
  +body = BODY(len, t, s, lf)
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34x = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he3 = PJ.pa_3(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlx = PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h7l = PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h67 = PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h56 = PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h45 = PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h01 = PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h12 = PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h4l = N.lt_to_le(n(e4), n(len), N.lt_trans(n(e4), n(e5), n(len), h45, N.lt_trans(n(e5), n(e6), n(len), h56, N.lt_trans(n(e6), n(e7), n(len), h67, N.le_lt_trans(n(e7), n(lf), n(len), h7l, hlx)))))
  +h0l = N.lt_to_le(n(e0), n(len), N.lt_le_trans(n(e0), n(e4), n(len), N.lt_trans(n(e0), n(e1), n(e4), h01, N.lt_trans(n(e1), n(e2), n(e4), h12, N.lt_trans(n(e2), n(e3), n(e4), h23, h34x))), h4l))
  +h3 = {%he2 : {Nat.is_le(_, n(e3)) == True{} : Bool}; C.succ_le(n(e2), n(e3), h23) : {Nat.is_le(n((e2 + 1 : U32)), n(e3)) == True{} : Bool}}
  +h34 = {%he3 : {Nat.is_le(n(e3), _) == True{} : Bool}; N.le_add_r(n(e3), 1n) : {Nat.is_le(n(e3), n((e3 + 1 : U32))) == True{} : Bool}}
  +h4 = {%he3 : {Nat.is_le(_, n(e4)) == True{} : Bool}; C.succ_le(n(e3), n(e4), h34x) : {Nat.is_le(n((e3 + 1 : U32)), n(e4)) == True{} : Bool}}
  +hal = PJ.pa_al(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +f0 = FLD(len, t, n(s), n(e0))
  +f1 = FLD(len, t, CU.nx(e0), n(e1))
  +f2 = FLD(len, t, CU.nx(e1), n(e2))
  +f5 = FLD(len, t, CU.nx(e4), n(e5))
  +f6 = FLD(len, t, CU.nx(e5), n(e6))
  +g3 = F3(len, t, e2, e3)
  +g4 = F4(len, t, e3, e4)
  +hpf = {%he2 : {J.pfs(body) == [f0, f1, f2, Norm.chars(D.slice(X, _, Nat.sub(n(e3), _))), g4, f5, f6, ""] : List<&2, String>};
    %he3 : {J.pfs(body) == [f0, f1, f2, FLD(len, t, CU.nx(e2), n(e3)), Norm.chars(D.slice(X, _, Nat.sub(n(e4), _))), f5, f6, ""] : List<&2, String>};
    CU.pass_fields(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp) : {J.pfs(body) == [f0, f1, f2, g3, g4, f5, f6, ""] : List<&2, String>}}
  +hs0 = W.and_l(Nat.is_le(n(s), n(e0)), True{}, W.and_tt(Nat.is_le(n(s), n(e0)), True{}, PJ.lf_s0(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), {==}))
  +hlt0 = {%U.is_lt_to_nat(s, e0) : {_ == True{} : Bool}; hse : {Nat.is_lt(n(s), n(e0)) == True{} : Bool}}
  +h0 = ne_chars(D.slice(X, n(s), Nat.sub(n(e0), n(s))),
    %Equal.sym(Nat, List.length(&2, U32, D.slice(X, n(s), Nat.sub(n(e0), n(s)))), Nat.sub(n(e0), n(s)), LP.slice_len(X, n(s), Nat.sub(n(e0), n(s)),
      %Equal.sym(Nat, Nat.add(n(s), Nat.sub(n(e0), n(s))), n(e0), N.le_sub_add(n(s), n(e0), hs0)) : {Nat.is_le(_, List.length(&2, U32, X)) == True{} : Bool};
      %LP.len_x(len, t, d, hok) : {Nat.is_le(n(e0), _) == True{} : Bool};
      h0l)) : {Nat.is_lt(0n, _) == True{} : Bool};
    LP.pos_sub(n(s), n(e0), hlt0))
  +offv = Nat.min(a0, String.length(r0))
  +basesv = B.Bases.of_fasta(CD.letters(r0, a0, b0))
  +hc = {%n_rl(e2, e3, h23, he2) : {J.ref_check(String.length(r0), offv, basesv, Nat.sub(n(pos), 1n), AA.bases_of(D.slice(X, n((e2 + 1 : U32)), _))) == Some{True{}} : Maybe<&2, Bool>};
    %bo_eq(D.slice(X, n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32)))) : {J.ref_check(String.length(r0), offv, basesv, Nat.sub(n(pos), 1n), _) == Some{True{}} : Maybe<&2, Bool>};
    hrc : {J.ref_check(String.length(r0), offv, basesv, Nat.sub(n(pos), 1n), AA.REF(X, (e2 + 1 : U32), e3)) == Some{True{}} : Maybe<&2, Bool>}}
  +hch = Equal.trans(String, c0, f0, WS.chrom_of(body),
    Equal.trans(String, c0, P.btext(len, t, s, (e0 - s : U32)), f0, Equal.sym(String, P.btext(len, t, s, (e0 - s : U32)), c0, hc0), btext_fld(len, t, s, e0, hs0)),
    Equal.trans(String, f0, B.Rec.field(J.pfs(body), 0n), WS.chrom_of(body),
      Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 0n), [f0, f1, f2, g3, g4, f5, f6, ""], J.pfs(body), Equal.sym(List<&2, String>, J.pfs(body), [f0, f1, f2, g3, g4, f5, f6, ""], hpf)),
      PF.pfs_field(body, 0n, {==})))
  +ht = {%hch : {WS.truthful(fa, _, Some{J.Known{String.length(r0), offv, CD.letters(r0, a0, b0)}}) == True{} : Bool};
    %hf : {WS.truthful(fa, c0, Some{CD.jtruth.k(_, a0, b0)}) == True{} : Bool};
    hjt : {WS.truthful(fa, WS.chrom_of(body), Some{J.Known{String.length(r0), offv, CD.letters(r0, a0, b0)}}) == True{} : Bool}}
  JG.fast_res(fa, body, f0, f1, f2, g3, g4, f5, f6, n(pos), AA.REF(X, (e2 + 1 : U32), e3), AA.ALTS(X, (e3 + 1 : U32), e4), String.length(r0), offv, CD.letters(r0, a0, b0),
    hpf, h0,
    PJ.pp_read(len, t, pos, e0, e1, CU.pass_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), PJ.pp_show(len, t, pos, e0, e1, CU.pass_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), PJ.pp_nz(len, t, pos, e0, e1, CU.pass_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)),
    PJ.ap_r(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)), PJ.ap_a(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)),
    PJ.ap_l(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)), PJ.ap_e(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)),
    PJ.ap_n(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)), PJ.ap_s3(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)),
    PJ.ap_s4(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)), PJ.ap_d(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal)),
    AA.alleles_norm(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, h4l, hal, offv, basesv, n(pos)),
    hc, ht)

# The run
# =======

law runn_eq:
  for +rp: P.RunP
  {NR.Run.n(P.mkRun(rp)) == (P.mkRun(rp), P.RunP.n(rp)) : NR.Run & Nat}

def runn_eq(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law n_spec:
  for +rp: P.RunP
  {R.RunSt.n(P.specRun(rp)) == P.RunP.n(rp) : Nat}

def n_spec(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# A run state's current CHROM.
def stc(st: R.RunSt) -> Maybe<&2, String>:
  match st:
    case R.RunSt{n0, i, h, c, e, l, b, k, o, ns, x}:
      c

law c_spec:
  for +rp: P.RunP
  {stc(P.specRun(rp)) == P.RunP.c(rp) : Maybe<&2, String>}

def c_spec(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law tick_n:
  for +st: R.RunSt
  {R.RunSt.n(R.tick(st)) == 1n+R.RunSt.n(st) : Nat}

def tick_n(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law tick_c:
  for +st: R.RunSt
  {stc(R.tick(st)) == stc(st) : Maybe<&2, String>}

def tick_c(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law inbody_settle:
  for +st: R.RunSt
  {R.RunSt.inbody(P.settle(st)) == R.RunSt.inbody(st) : Bool}

def inbody_settle(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      {==}
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, True{}}:
      {==}

# The spec's step on a body line (not stopped, in the body) whose judge
# leaves it as it is.
law body_step:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +A: String
  for +p: Nat
  for +chrom: String
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  for +hin: {P.RunP.i(rp) == True{} : Bool}
  for +hj: {L.judge(fa, B.Line.body(Norm.line(A))) == JG.RN(B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(A)))), B.Line.body(Norm.line(A))) : B.Res}
  for +hpos: {B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(A)))) == p : Nat}
  for +hf0: {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 0n) == chrom : String}
  for +hf1: {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 1n) == Nat.show(p) : String}
  for +hw0: {B.Rec.parts(dfs, o, B.Line.body(Norm.line(A))) == B.Whole{} : B.Parts}
  {L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) == R.body_line(JG.RN(p, B.Line.body(Norm.line(A))), R.tick(P.specRun(rp)), o, Norm.line(A), B.At{1n+P.RunP.n(rp), chrom, Nat.show(p)}, p) : R.RunSt}

def body_step(dfs, fa, o, rp, A, p, chrom, hx, hin, hj, hpos, hf0, hf1, hw0):
  +st = P.specRun(rp)
  +l = Norm.line(A)
  +bd = B.Line.body(l)
  +fs = B.Rec.fields(bd)
  +RHS = R.body_line(JG.RN(p, bd), R.tick(st), o, l, B.At{1n+P.RunP.n(rp), chrom, Nat.show(p)}, p)
  %Equal.sym(Bool, R.RunSt.halt(st), False{}, Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, WR.halt_spec(rp), hx)) :
    {L.line_step.go(_, fa, dfs, o, st, B.Text.line(A)) == RHS : R.RunSt}
  %Equal.sym(Bool, R.RunSt.inbody(st), True{}, Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, WR.ib_spec(rp), hin)) :
    {L.line_in(_, fa, dfs, o, R.tick(st), B.Text.line(A)) == RHS : R.RunSt}
  %LN.line_eq(A) : {L.body_in(B.Rec.parts(dfs, o, B.Line.body(_)), fa, o, R.tick(st), _, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(B.Rec.fields(B.Line.body(_)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(_)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(_)))) == RHS : R.RunSt}
  %Equal.sym(B.Parts, B.Rec.parts(dfs, o, bd), B.Whole{}, hw0) : {L.body_in(_, fa, o, R.tick(st), l, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == RHS : R.RunSt}
  %Equal.sym(B.Res, L.judge(fa, bd), JG.RN(B.Rec.pos(fs), bd), hj) :
    {R.body_line(_, R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == RHS : R.RunSt}
  %Equal.sym(Nat, B.Rec.pos(fs), p, hpos) :
    {R.body_line(JG.RN(_, bd), R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, _) == RHS : R.RunSt}
  %Equal.sym(String, B.Rec.field(fs, 0n), chrom, hf0) :
    {R.body_line(JG.RN(p, bd), R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), _, B.Rec.field(fs, 1n)}, p) == RHS : R.RunSt}
  %Equal.sym(String, B.Rec.field(fs, 1n), Nat.show(p), hf1) :
    {R.body_line(JG.RN(p, bd), R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), chrom, _}, p) == RHS : R.RunSt}
  %Equal.sym(Nat, R.RunSt.n(R.tick(st)), 1n+P.RunP.n(rp), Equal.trans(Nat, R.RunSt.n(R.tick(st)), 1n+R.RunSt.n(st), 1n+P.RunP.n(rp), tick_n(st),
      Equal.cong(Nat, Nat, z => 1n+z, R.RunSt.n(st), P.RunP.n(rp), n_spec(rp)))) :
    {R.body_line(JG.RN(p, bd), R.tick(st), o, l, B.At{_, chrom, Nat.show(p)}, p) == RHS : R.RunSt}
  {==}

# The line's bytes for run_fast_done
# ==================================

def KK(+at: U32, +lf: U32) -> U32:
  (lf + 1 - at : U32)

law k_n:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +lf: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool}
  for +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  {n(KK(at, lf)) == Nat.sub(Nat.add(n(lf), 1n), n(at)) : Nat}

def k_n(len, t, d, at, lf, hok, hal, hlt):
  +hinc = LP.inc_len(len, t, d, lf, hok, hlt)
  +hle1 = {%Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), hinc) : {Nat.is_le(n(at), _) == True{} : Bool}; N.le_trans(n(at), n(lf), Nat.add(n(lf), 1n), hal, N.le_add_r(n(lf), 1n)) : {Nat.is_le(n(at), n((lf + 1 : U32))) == True{} : Bool}}
  %Equal.sym(Nat, n(KK(at, lf)), Nat.sub(n((lf + 1 : U32)), n(at)), LP.sub_u((lf + 1 : U32), at, hle1)) : {_ == Nat.sub(Nat.add(n(lf), 1n), n(at)) : Nat}
  %Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), hinc) : {Nat.sub(_, n(at)) == Nat.sub(Nat.add(n(lf), 1n), n(at)) : Nat}
  {==}

law k_fit:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +lf: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool}
  for +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  {Nat.is_le(Nat.add(n(at), n(KK(at, lf))), n(len)) == True{} : Bool}

def k_fit(len, t, d, at, lf, hok, hal, hlt):
  +hle = N.le_trans(n(at), n(lf), Nat.add(n(lf), 1n), hal, N.le_add_r(n(lf), 1n))
  %Equal.sym(Nat, n(KK(at, lf)), Nat.sub(Nat.add(n(lf), 1n), n(at)), k_n(len, t, d, at, lf, hok, hal, hlt)) : {Nat.is_le(Nat.add(n(at), _), n(len)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n(at), Nat.sub(Nat.add(n(lf), 1n), n(at))), Nat.add(n(lf), 1n), N.le_sub_add(n(at), Nat.add(n(lf), 1n), hle)) : {Nat.is_le(_, n(len)) == True{} : Bool}
  C.succ_le(n(lf), n(len), hlt)

# The line's text with its LF is the bytes at .. lf.
law k_text:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +lf: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {U32.is_le(at, len) == True{} : Bool}
  for +hfl: {D.first(xs(len, t), n(at), n(len), 10) == n(lf) : Nat}
  for +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool}
  for +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  {P.btext(len, t, at, KK(at, lf)) == B.Line.text(Norm.line(P.btext(len, t, at, (lf - at : U32)))) : String}

def k_text(len, t, d, at, lf, hok, hs, hfl, hal, hlt):
  +X = xs(len, t)
  +hlf = ALP.has_get(X, n(lf), 10,
    %Equal.sym(Nat, n(lf), D.first(X, n(at), n(len), 10), Equal.sym(Nat, D.first(X, n(at), n(len), 10), n(lf), hfl)) : {D.has(X, _, 10) == True{} : Bool};
    BL.first_hit(X, n(at), n(len), 10, LI.u2n(at, len, hs), %LP.len_x(len, t, d, hok) : {Nat.is_le(n(len), _) == True{} : Bool}; N.le_refl(n(len)),
      %Equal.sym(Nat, D.first(X, n(at), n(len), 10), n(lf), hfl) : {Nat.is_lt(_, n(len)) == True{} : Bool}; hlt))
  %Equal.sym(Nat, n(KK(at, lf)), Nat.sub(Nat.add(n(lf), 1n), n(at)), k_n(len, t, d, at, lf, hok, hal, hlt)) :
    {NR.chars(D.slice(X, n(at), _)) == B.Line.text(Norm.line(P.btext(len, t, at, (lf - at : U32)))) : String}
  %Equal.sym(String, P.btext(len, t, at, (lf - at : U32)), CU.fld(X, n(at), n(lf)), btext_fld(len, t, at, lf, hal)) : {NR.chars(D.slice(X, n(at), Nat.sub(Nat.add(n(lf), 1n), n(at)))) == B.Line.text(Norm.line(_)) : String}
  %LSS.chars_norm(D.slice(X, n(at), Nat.sub(Nat.add(n(lf), 1n), n(at)))) :
    {_ == B.Line.text(CU.lline(X, at, lf)) : String}
  Equal.sym(String, B.Line.text(CU.lline(X, at, lf)), Norm.chars(D.slice(X, n(at), Nat.sub(Nat.add(n(lf), 1n), n(at)))), CU.line_text(X, at, lf, hlf, hal))

# The ticked run's CHROM.
law c_tick:
  for +rp: P.RunP
  for +rp1: P.RunP
  for +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt}
  {P.RunP.c(rp1) == P.RunP.c(rp) : Maybe<&2, String>}

def c_tick(rp, rp1, s1):
  %c_spec(rp1) : {_ == P.RunP.c(rp) : Maybe<&2, String>}
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {stc(_) == P.RunP.c(rp) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, stc(R.tick(P.specRun(rp))), stc(P.specRun(rp)), tick_c(P.specRun(rp))) : {_ == P.RunP.c(rp) : Maybe<&2, String>}
  c_spec(rp)

law sub_succ:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.sub(Nat.add(b, 1n), a) == Nat.add(Nat.sub(b, a), 1n) : Nat}

def sub_succ(a, b, h):
  +x = Nat.sub(b, a)
  %N.le_sub_add(a, b, h) : {Nat.sub(Nat.add(_, 1n), a) == Nat.add(x, 1n) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, x), 1n), Nat.add(a, Nat.add(x, 1n)), N.add_assoc(a, x, 1n)) : {Nat.sub(_, a) == Nat.add(x, 1n) : Nat}
  N.sub_add_l(a, Nat.add(x, 1n))

# The line's length plus its LF, against a bound y + 1 (y a word whose
# successor does not wrap).
law k_le:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +lf: U32
  for +y: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool}
  for +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  for +hsm: {U32.is_le((lf - at : U32), y) == True{} : Bool}
  for +hy: {n(U32.inc(y)) == Nat.add(n(y), 1n) : Nat}
  {U32.is_le(KK(at, lf), U32.inc(y)) == True{} : Bool}

def k_le(len, t, d, at, lf, y, hok, hal, hlt, hsm, hy):
  LP.le_u(KK(at, lf), U32.inc(y),
    %Equal.sym(Nat, n(KK(at, lf)), Nat.sub(Nat.add(n(lf), 1n), n(at)), k_n(len, t, d, at, lf, hok, hal, hlt)) : {Nat.is_le(_, n(U32.inc(y))) == True{} : Bool};
    %Equal.sym(Nat, Nat.sub(Nat.add(n(lf), 1n), n(at)), Nat.add(Nat.sub(n(lf), n(at)), 1n), sub_succ(n(at), n(lf), hal)) : {Nat.is_le(_, n(U32.inc(y))) == True{} : Bool};
    %LP.sub_u(lf, at, hal) : {Nat.is_le(Nat.add(_, 1n), n(U32.inc(y))) == True{} : Bool};
    %Equal.sym(Nat, n(U32.inc(y)), Nat.add(n(y), 1n), hy) : {Nat.is_le(Nat.add(n((lf - at : U32)), 1n), _) == True{} : Bool};
    N.le_add_mono_r(1n, n((lf - at : U32)), n(y), LI.u2n((lf - at : U32), y, hsm)))

# The same with y below a word z (so y's successor does not wrap); kept
# abstract so the checker never expands the literal bounds.
law k_le_z:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +lf: U32
  for +y: U32
  for +z: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool}
  for +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  for +hsm: {U32.is_le((lf - at : U32), y) == True{} : Bool}
  for +hyz: {U32.is_lt(y, z) == True{} : Bool}
  {U32.is_le(KK(at, lf), U32.inc(y)) == True{} : Bool}

def k_le_z(len, t, d, at, lf, y, z, hok, hal, hlt, hsm, hyz):
  k_le(len, t, d, at, lf, y, hok, hal, hlt, hsm, U.to_nat_inc_lt(y, z, hyz))

# The fields judging reads, from the line's cut.
def FS(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> List<&2, String>:
  B.Rec.fields(BODY(len, t, s, lf))

law fs_f:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: U32
  for +pos: U32
  for +e0: U32
  for +e1: U32
  for +e2: U32
  for +e3: U32
  for +e4: U32
  for +e5: U32
  for +e6: U32
  for +e7: U32
  for +lf: U32
  for +i: Nat
  for +hi: {Nat.is_lt(i, 7n) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {U32.is_le(s, len) == True{} : Bool}
  for +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)
  {B.Rec.field(FS(len, t, s, lf), i) == B.Rec.field([FLD(len, t, n(s), n(e0)), FLD(len, t, CU.nx(e0), n(e1)), FLD(len, t, CU.nx(e1), n(e2)), FLD(len, t, CU.nx(e2), n(e3)), FLD(len, t, CU.nx(e3), n(e4)), FLD(len, t, CU.nx(e4), n(e5)), FLD(len, t, CU.nx(e5), n(e6)), ""], i) : String}

def fs_f(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, i, hi, hok, hs, hp):
  +body = BODY(len, t, s, lf)
  %PF.pfs_field(body, i, hi) : {_ == B.Rec.field([FLD(len, t, n(s), n(e0)), FLD(len, t, CU.nx(e0), n(e1)), FLD(len, t, CU.nx(e1), n(e2)), FLD(len, t, CU.nx(e2), n(e3)), FLD(len, t, CU.nx(e3), n(e4)), FLD(len, t, CU.nx(e4), n(e5)), FLD(len, t, CU.nx(e5), n(e6)), ""], i) : String}
  Equal.cong(List<&2, String>, String, z => B.Rec.field(z, i), J.pfs(body), [FLD(len, t, n(s), n(e0)), FLD(len, t, CU.nx(e0), n(e1)), FLD(len, t, CU.nx(e1), n(e2)), FLD(len, t, CU.nx(e2), n(e3)), FLD(len, t, CU.nx(e3), n(e4)), FLD(len, t, CU.nx(e4), n(e5)), FLD(len, t, CU.nx(e5), n(e6)), ""],
    CU.pass_fields(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))

law hpos_l:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: U32
  for +pos: U32
  for +e0: U32
  for +e1: U32
  for +e2: U32
  for +e3: U32
  for +e4: U32
  for +e5: U32
  for +e6: U32
  for +e7: U32
  for +lf: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {U32.is_le(s, len) == True{} : Bool}
  for +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)
  {B.Rec.pos(FS(len, t, s, lf)) == n(pos) : Nat}

def hpos_l(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp):
  %Equal.sym(String, B.Rec.field(FS(len, t, s, lf), 1n), B.Rec.field([FLD(len, t, n(s), n(e0)), FLD(len, t, CU.nx(e0), n(e1)), FLD(len, t, CU.nx(e1), n(e2)), FLD(len, t, CU.nx(e2), n(e3)), FLD(len, t, CU.nx(e3), n(e4)), FLD(len, t, CU.nx(e4), n(e5)), FLD(len, t, CU.nx(e5), n(e6)), ""], 1n), fs_f(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, 1n, {==}, hok, hs, hp)) : {Maybe.default(&2, Nat, B.Pos.read(_), 0n) == n(pos) : Nat}
  %Equal.sym(Maybe<&2, Nat>, B.Pos.read(FLD(len, t, CU.nx(e0), n(e1))), Some{n(pos)}, PJ.pp_read(len, t, pos, e0, e1, CU.pass_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))) : {Maybe.default(&2, Nat, _, 0n) == n(pos) : Nat}
  {==}

# The hit
# =======

def AofL(+len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32) -> String:
  P.btext(len, t, at, (lf - at : U32))

def BL0(+o: B.Opts, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32, +pos: U32, +chrom: String) -> R.RunSt:
  R.body_line(JG.RN(n(pos), B.Line.body(Norm.line(AofL(len, t, at, lf)))), P.specRun(rp1), o, Norm.line(AofL(len, t, at, lf)), B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos))

def fhit.w(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(n(pos), 1n), CD.bases_of(D.slice(xs(len, t), n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +hfl: {D.first(xs(len, t), n(at), n(len), 10) == n(lf) : Nat},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +i2: {PR.RunInv(rp2) == True{} : Bool},
  +sp2: {P.settle(P.specRun(rp2)) == P.settle(BL0(o, rp1, len, t, at, lf, pos, P.btext(len, t, at, (e0 - at : U32)))) : R.RunSt},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(AofL(len, t, at, lf)) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(AofL(len, t, at, lf)) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.Src.of(hold, C.BT(len, t), (lf + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, CD.mkWin(fa, wp), None{}, False{}, dfs}}):
  match sl:
    case (hsp, q):
      match q:
        case (hn, q2):
          match q2:
            case (hle, hby):
              +A = AofL(len, t, at, lf)
              +l = Norm.line(A)
              +X = xs(len, t)
              +chrom = P.btext(len, t, at, (e0 - at : U32))
              +bd = B.Line.body(l)
              +hfa = btext_fld(len, t, at, lf, hal)
              +hs0 = PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
              +hj = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {L.judge(fa, B.Line.body(Norm.line(_))) == JG.RN(B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(_)))), B.Line.body(Norm.line(_))) : B.Res};
                hit_judge(fa, len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c0, a0, b0, r0, hok, hs, hp, hse, hf, hc0, hrc, hjt) : {L.judge(fa, bd) == JG.RN(B.Rec.pos(B.Rec.fields(bd)), bd) : B.Res}}
              +hpos = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(_)))) == n(pos) : Nat};
                hpos_l(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp) : {B.Rec.pos(B.Rec.fields(bd)) == n(pos) : Nat}}
              +hf0 = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(_))), 0n) == chrom : String};
                %Equal.sym(String, chrom, FLD(len, t, n(at), n(e0)), btext_fld(len, t, at, e0, hs0)) : {B.Rec.field(FS(len, t, at, lf), 0n) == _ : String};
                fs_f(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, 0n, {==}, hok, hs, hp) : {B.Rec.field(B.Rec.fields(bd), 0n) == chrom : String}}
              +hf1 = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(_))), 1n) == Nat.show(n(pos)) : String};
                %Equal.sym(String, Nat.show(n(pos)), FLD(len, t, CU.nx(e0), n(e1)), PJ.pp_show(len, t, pos, e0, e1, CU.pass_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))) : {B.Rec.field(FS(len, t, at, lf), 1n) == _ : String};
                fs_f(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, 1n, {==}, hok, hs, hp) : {B.Rec.field(B.Rec.fields(bd), 1n) == Nat.show(n(pos)) : String}}
              +E1 = {%Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {R.body_line(JG.RN(n(pos), bd), _, o, l, B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt};
                %Equal.sym(Nat, P.RunP.n(rp1), 1n+P.RunP.n(rp), n1) : {R.body_line(JG.RN(n(pos), bd), R.tick(P.specRun(rp)), o, l, B.At{_, chrom, Nat.show(n(pos))}, n(pos)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt};
                Equal.sym(R.RunSt, L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), R.body_line(JG.RN(n(pos), bd), R.tick(P.specRun(rp)), o, l, B.At{1n+P.RunP.n(rp), chrom, Nat.show(n(pos))}, n(pos)), body_step(dfs, fa, o, rp, A, n(pos), chrom, hx, hin, hj, hpos, hf0, hf1, MW.hw_line(dfs, o, len, t, d, hok, at, lf, hs, hfl, hal, hlt, hmv))) :
                {BL0(o, rp1, len, t, at, lf, pos, chrom) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt}}
              +hrun = Equal.trans(R.RunSt, P.settle(P.specRun(rp2)), P.settle(BL0(o, rp1, len, t, at, lf, pos, chrom)), P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A))),
                sp2, Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), BL0(o, rp1, len, t, at, lf, pos, chrom), L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), E1))
              +BLs = R.body_line(JG.RN(n(pos), bd), P.specRun(rp1), o, l, B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos))
              +hib = {%inbody_settle(P.specRun(rp2)) : {_ == True{} : Bool};
                %Equal.sym(R.RunSt, P.settle(P.specRun(rp2)), P.settle(BL0(o, rp1, len, t, at, lf, pos, chrom)), sp2) : {R.RunSt.inbody(_) == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(P.settle(BLs)), R.RunSt.inbody(BLs), inbody_settle(BLs)) : {_ == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(BLs), R.RunSt.inbody(P.specRun(rp1)), IB.ib_body_line(JG.RN(n(pos), bd), P.specRun(rp1), o, l, B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos))) : {_ == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp1)), P.RunP.i(rp1), WR.ib_spec(rp1)) : {_ == True{} : Bool};
                hin1 : {R.RunSt.inbody(P.specRun(rp2)) == True{} : Bool}}
              +Xd = B.Defs.line(dfs, B.Line.body(B.Text.line(A)))
              +hd = {%Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp)), True{}, Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp)), P.RunP.i(rp), True{}, WR.ib_spec(rp), hin)) :
                  {dfs == Bool.pick(B.Defs, _, dfs, Xd) : B.Defs};
                {==} : {dfs == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, Xd) : B.Defs}}
              HX.went_h(hold,dfs, dfs, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hsp, hle, hn, hal, hlt, LP.inc_len(len, t, d, lf, hok, hlt), i2, hrun,
                W.or_l(R.RunSt.inbody(P.specRun(rp2)), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), hib), hx, hd)

# Facts for against_hit
# =====================

# ALT's end is inside the buffer.
def e4_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(n(e4), n(len)) == True{} : Bool}:
  +hlx = PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h7l = PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h67 = PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h56 = PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h45 = PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  N.lt_to_le(n(e4), n(len), N.lt_trans(n(e4), n(e5), n(len), h45, N.lt_trans(n(e5), n(e6), n(len), h56, N.lt_trans(n(e6), n(e7), n(len), h67, N.le_lt_trans(n(e7), n(lf), n(len), h7l, hlx)))))

# CHROM's end is inside the buffer.
def e0_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(n(e0), n(len)) == True{} : Bool}:
  +h01 = PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h12 = PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34x = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  N.lt_to_le(n(e0), n(len), N.lt_le_trans(n(e0), n(e4), n(len), N.lt_trans(n(e0), n(e1), n(e4), h01, N.lt_trans(n(e1), n(e2), n(e4), h12, N.lt_trans(n(e2), n(e3), n(e4), h23, h34x))), e4_le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))

# REF and ALT pass the alleles' tests.
def apass(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  PJ.APT(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4):
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34x = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he3 = PJ.pa_3(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h3 = {%he2 : {Nat.is_le(_, n(e3)) == True{} : Bool}; C.succ_le(n(e2), n(e3), h23) : {Nat.is_le(n((e2 + 1 : U32)), n(e3)) == True{} : Bool}}
  +h34 = {%he3 : {Nat.is_le(n(e3), _) == True{} : Bool}; N.le_add_r(n(e3), 1n) : {Nat.is_le(n(e3), n((e3 + 1 : U32))) == True{} : Bool}}
  +h4 = {%he3 : {Nat.is_le(_, n(e4)) == True{} : Bool}; C.succ_le(n(e3), n(e4), h34x) : {Nat.is_le(n((e3 + 1 : U32)), n(e4)) == True{} : Bool}}
  +hal = PJ.pa_al(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  AA.alleles_pass(len, t, d, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, hok, h3, h34, h4, e4_le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp), hal)

# REF's bytes are upper-case bases.
def ref_up(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {CD.up(D.slice(xs(len, t), n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32)))) == True{} : Bool}:
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +sl = D.slice(xs(len, t), n((e2 + 1 : U32)), Nat.sub(n(e3), n((e2 + 1 : U32))))
  %Equal.sym(Nat, n((e3 - e2 - 1 : U32)), Nat.sub(n(e3), n((e2 + 1 : U32))), n_rl(e2, e3, h23, he2)) : {CD.up(D.slice(xs(len, t), n((e2 + 1 : U32)), _)) == True{} : Bool}
  %up_eq(sl) : {_ == True{} : Bool}
  PJ.ap_up(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, apass(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))

# REF is not empty.
def ref_pos(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {U32.is_lt(0, (e3 - e2 - 1 : U32)) == True{} : Bool}:
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  %Equal.sym(Bool, U32.is_lt(0, (e3 - e2 - 1 : U32)), Nat.is_lt(n(0), n((e3 - e2 - 1 : U32))), U.is_lt_to_nat(0, (e3 - e2 - 1 : U32))) : {_ == True{} : Bool}
  %Equal.sym(Nat, n((e3 - e2 - 1 : U32)), Nat.sub(n(e3), n((e2 + 1 : U32))), n_rl(e2, e3, h23, he2)) : {Nat.is_lt(n(0), _) == True{} : Bool}
  LP.pos_sub(n((e2 + 1 : U32)), n(e3), PJ.ap_lt(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4, apass(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))

# REF is inside the buffer.
def ref_fit(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: PASS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(Nat.add(n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32))), n(len)) == True{} : Bool}:
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34x = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he2 = PJ.pa_2(len, t, e2, e3, e4, CU.pass_alleles(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h3 = {%he2 : {Nat.is_le(_, n(e3)) == True{} : Bool}; C.succ_le(n(e2), n(e3), h23) : {Nat.is_le(n((e2 + 1 : U32)), n(e3)) == True{} : Bool}}
  %Equal.sym(Nat, n((e3 - e2 - 1 : U32)), Nat.sub(n(e3), n((e2 + 1 : U32))), n_rl(e2, e3, h23, he2)) : {Nat.is_le(Nat.add(n((e2 + 1 : U32)), _), n(len)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n((e2 + 1 : U32)), Nat.sub(n(e3), n((e2 + 1 : U32)))), n(e3), N.le_sub_add(n((e2 + 1 : U32)), n(e3), h3)) : {Nat.is_le(_, n(len)) == True{} : Bool}
  N.lt_to_le(n(e3), n(len), N.lt_le_trans(n(e3), n(e4), n(len), h34x, e4_le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))

# The hit after its tick: the run's fast_done, then the source steps.
def fhit.d(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(n(pos), 1n), CD.bases_of(D.slice(xs(len, t), n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +hfl: {D.first(xs(len, t), n(at), n(len), 10) == n(lf) : Nat},
  fd: &p2: P.RunP -> ({NR.fast_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), n(pos), C.BT(len, t), at, KK(at, lf)) == (P.mkRun(p2), C.BT(len, t)) : NR.Run & D.Bytes}
  & ({PR.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Normalized{}, n(pos), B.Line.body(Norm.line(AofL(len, t, at, lf))), False{}}, P.specRun(rp1), o, Norm.line(AofL(len, t, at, lf)), B.At{P.RunP.n(rp1), P.btext(len, t, at, (e0 - at : U32)), Nat.show(n(pos))}, n(pos))) : R.RunSt})),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.fast.hit(o, (P.mkRun(rp1), P.RunP.n(rp1)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
  match fd:
    case (+rp2, q):
      match q:
        case (efd, q2):
          match q2:
            case (i2, sp2):
              %Equal.sym(NR.Run & D.Bytes, NR.fast_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), n(pos), C.BT(len, t), at, KK(at, lf)), (P.mkRun(rp2), C.BT(len, t)), efd) :
                S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.done.b(o, _, (lf + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
              fhit.w(hold, dfs, fa, T, cs, O, N, o, rp, rp1, rp2, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c0, a0, b0, r0,
                hw, hr, hg, hx, hin, hok, hs, hmv, hp, hse, hf, hc0, hrc, hjt, hal, hlt, hfl, s1, n1, hin1, i2, sp2,
                LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt), hnr)

# The hit with the line's tick done (rp1).
def fhit.t(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(n(pos), 1n), CD.bases_of(D.slice(xs(len, t), n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.fast.hit(o, NR.Run.n(NR.tick(P.mkRun(rp))), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
  +A = AofL(len, t, at, lf)
  +l = Norm.line(A)
  +chrom = P.btext(len, t, at, (e0 - at : U32))
  +hfl = PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt = PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hjr = j_range(len, t, d, at, lf, hok, hs, Equal.sym(Nat, D.first(xs(len, t), n(at), n(len), 10), n(lf), hfl))
  +hal = W.and_l(Nat.is_le(n(at), n(lf)), Nat.is_le(n(lf), n(len)), hjr)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hc1 = Equal.trans(Maybe<&2, String>, P.RunP.c(rp1), P.RunP.c(rp), Some{chrom}, c_tick(rp, rp1, s1), hcr)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.fast.hit(o, NR.Run.n(_), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), runn_eq(rp1)) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.fast.hit(o, _, pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
  fhit.d(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c0, a0, b0, r0, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hmv, hp, hse, hcr, hsm, hf, hc0, hrc, hjt, rp1, s1, n1, hin1, hal, hlt, hfl,
    PR.run_fast_done(rp1, o, l, n(pos), chrom, len, t, d, at, KK(at, lf), i1, hin1, hx1, hok,
      k_fit(len, t, d, at, lf, hok, hal, hlt), k_text(len, t, d, at, lf, hok, hs, hfl, hal, hlt), hc1, hbig1,
      k_le_z(len, t, d, at, lf, 268435456, 268435457, hok, hal, hlt, hsm, {==})), hnr)

# The fast path's hit: the line is written as it came.
def fhit(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(n(pos), 1n), CD.bases_of(D.slice(xs(len, t), n((e2 + 1 : U32)), n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  tk: WR.TKW(rp),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.fast.hit(o, Norm.ticked(P.mkRun(rp)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
  match tk:
    case (+rp1, q):
      match q:
        case (et, q2):
          match q2:
            case (i1, q3):
              match q3:
                case (s1, q4):
                  match q4:
                    case (n1, q5):
                      match q5:
                        case (obl1, ow1):
                          fhit.t(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c0, a0, b0, r0, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hmv, hp, hse, hcr, hsm, hf, hc0, hrc, hjt, rp1, et, i1, s1, n1, obl1, hnr)
