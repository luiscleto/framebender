import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
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
import ./proof_c_advf.bend as AF
import ./proof_c_tan.bend as TN
import ./proof_c_text.bend as TX
import ./proof_c_text_w.bend as WW
import ./proof_c_take.bend as TK
import ./proof_c_tk.bend as TKK
import ./proof_b_enc.bend as EN
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_adv_tostr.bend as TSS
import ../lawful-bytes/proof_same.bend as SMB
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Phase C: adv_ok's rewrite path once the window holds the record and REF
# matches it (norm.bend fix.hit .. fix.tick): the rewrite, or (any doubt)
# the decoded path. Every variable is reusable.

def TNEW(+len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32, +pos: U32, +als: List<&2, NX.Ap>, +wl: U32, +wt: AT.Tree<U32>, +offu: U32, +k: U32, +tr: U32, +dl: Nat) -> String:
  B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), als, pos), Q.VW(Q.xs(len, t), Q.xs(wl, wt), als, pos, offu, k, tr, dl))

def ae.k(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  h: {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), PE.REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))) ->
  {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}:
  (eq, r1) = h
  eq

# The alleles: REF, then the ALTs.
def alsE(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) -> {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}:
  ae.k(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))

# x <= y < len: bytes x .. y are inside the buffer.
def kbg(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: U32, +y: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hxy: {Nat.is_le(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(y), U32.to_nat(len)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(U32.to_nat(x), U32.to_nat(((y + 1 : U32) - x : U32))), U32.to_nat(len)) == True{} : Bool}:
  +hinc = LP.inc_len(len, t, d, y, hok, hy)
  +hx1 = {%Equal.sym(Nat, U32.to_nat((y + 1 : U32)), Nat.add(U32.to_nat(y), 1n), hinc) : {Nat.is_le(U32.to_nat(x), _) == True{} : Bool}; N.le_trans(U32.to_nat(x), U32.to_nat(y), Nat.add(U32.to_nat(y), 1n), hxy, N.le_add_r(U32.to_nat(y), 1n)) : {Nat.is_le(U32.to_nat(x), U32.to_nat((y + 1 : U32))) == True{} : Bool}}
  %Equal.sym(Nat, U32.to_nat(((y + 1 : U32) - x : U32)), Nat.sub(U32.to_nat((y + 1 : U32)), U32.to_nat(x)), LP.sub_u((y + 1 : U32), x, hx1)) : {Nat.is_le(Nat.add(U32.to_nat(x), _), U32.to_nat(len)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(U32.to_nat(x), Nat.sub(U32.to_nat((y + 1 : U32)), U32.to_nat(x))), U32.to_nat((y + 1 : U32)), N.le_sub_add(U32.to_nat(x), U32.to_nat((y + 1 : U32)), hx1)) : {Nat.is_le(_, U32.to_nat(len)) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat((y + 1 : U32)), Nat.add(U32.to_nat(y), 1n), hinc) : {Nat.is_le(_, U32.to_nat(len)) == True{} : Bool}
  C.succ_le(U32.to_nat(y), U32.to_nat(len), hy)

# The writer's slices are inside the line.
def kb1(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(TX.K1(s, e0))), U32.to_nat(len)) == True{} : Bool}:
  kbg(len, t, d, s, e0, hok, PJ.lf_s0(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_le_trans(U32.to_nat(e0), U32.to_nat(e4), U32.to_nat(len), N.lt_trans(U32.to_nat(e0), U32.to_nat(e1), U32.to_nat(e4), PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e1), U32.to_nat(e2), U32.to_nat(e4), PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e2), U32.to_nat(e3), U32.to_nat(e4), PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))), AF.e4le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

def kb2(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(TX.K2(e1, e2))), U32.to_nat(len)) == True{} : Bool}:
  kbg(len, t, d, e1, e2, hok, N.lt_to_le(U32.to_nat(e1), U32.to_nat(e2), PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), N.lt_le_trans(U32.to_nat(e2), U32.to_nat(e4), U32.to_nat(len), N.lt_trans(U32.to_nat(e2), U32.to_nat(e3), U32.to_nat(e4), PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), AF.e4le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

def kb3(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(TX.K3(e4, lf))), U32.to_nat(len)) == True{} : Bool}:
  kbg(len, t, d, e4, lf, hok, N.lt_to_le(U32.to_nat(e4), U32.to_nat(lf), N.lt_le_trans(U32.to_nat(e4), U32.to_nat(e7), U32.to_nat(lf), N.lt_trans(U32.to_nat(e4), U32.to_nat(e5), U32.to_nat(e7), PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e5), U32.to_nat(e6), U32.to_nat(e7), PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))), PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))), PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

# A line declined after the window was unfolded: the decoded path.
def hdec(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, fneed)):
  %Equal.sym(Norm.Win, Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, CD.mkWin(fa, CD.WPKnown{c, a, b}), emk) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, DE.CX(rest, pd, eof), _, fneed))
  DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig)

# The take: the run's step, then the line's (proof_c_tk.bend).
def hfits.t(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(TNEW(len, t, at, lf, pos, PE.REF(e2, e3) <> Q.TL(als), U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool},
  +ef: {U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.fits(True{}, back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)})):
  TKK.take(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hne, ef)

def hfits(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(TNEW(len, t, at, lf, pos, PE.REF(e2, e3) <> Q.TL(als), U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool},
  +f: Bool, +ef: {U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)) == f : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.fits(f, back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)})):
  match f:
    case False{}:
      %Equal.sym(Norm.Win, Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, CD.mkWin(fa, CD.WPKnown{c, a, b}), emk) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.to_str(o, P.mkRun(rp), C.BT(len, t), at, back, DE.CX(rest, pd, eof), _, False{}))
      TSS.to_ms_went(fa, T, cs, O, N, o, rp, Con{LI.SB(len, t, d, at), rest}, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, back, False{}, hw, hr, hg, hx)
    case True{}:
      hfits.t(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hne, ef)

# The line was rewritten and is not the line as it came.
def hmain(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(TNEW(len, t, at, lf, pos, PE.REF(e2, e3) <> Q.TL(als), U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.ne(False{}, back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(sl, st), C.BT(len, t), DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, fneed)):
  %Equal.sym(NR.Run & U32, Norm.Run.oblen(P.mkRun(rp)), (P.mkRun(rp), P.RunP.obl(rp)), SLW.oblen_eq(rp)) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.len(back, o, _, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(len, t), BY.len(C.BT(sl, st)), DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}))
  hfits(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hne, U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)), {==})

# Lengths differ: the new text is not the line's body.
def ne_len(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hl: {U32.is_eq(sl, ((lf + 1 : U32) - at : U32)) == False{} : Bool}) ->
  {String.eq(TNEW(len, t, at, lf, pos, PE.REF(e2, e3) <> Q.TL(als), U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool}:
  TK.ne_len_t(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, okw, TNEW(len, t, at, lf, pos, PE.REF(e2, e3) <> Q.TL(als), U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), TK.hpk_w(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, r, a, b, CA.find_bytes(fa, c, r, hb, hf), hrc, hfs, k, tr, dl, hz, sl, st, pk), hl)

# The bytes differ: the new text is not the line's body.
def ne_eq(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hl: {U32.is_eq(sl, ((lf + 1 : U32) - at : U32)) == True{} : Bool},
  +he: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl))) == False{} : Bool}) ->
  {String.eq(TNEW(len, t, at, lf, pos, PE.REF(e2, e3) <> Q.TL(als), U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool}:
  TK.ne_eq_t(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, okw, TNEW(len, t, at, lf, pos, PE.REF(e2, e3) <> Q.TL(als), U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), TK.hpk_w(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, r, a, b, CA.find_bytes(fa, c, r, hb, hf), hrc, hfs, k, tr, dl, hz, sl, st, pk), hl, he)

def heq(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String}, +hl: {U32.is_eq(sl, ((lf + 1 : U32) - at : U32)) == True{} : Bool},
  +e: Bool, +ee: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl))) == e : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.ne(e, back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(sl, st), C.BT(len, t), DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, fneed)):
  match e:
    case True{}:
      hdec(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk)
    case False{}:
      hmain(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, ne_eq(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hl, ee))

def hcmp(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String}, +g: Bool, +eg: {U32.is_eq(sl, ((lf + 1 : U32) - at : U32)) == g : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.cmp.k(back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, Norm.fix.cmp.if(g, C.BT(sl, st), C.BT(len, t), at, sl), DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, fneed)):
  match g:
    case False{}:
      hmain(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, ne_len(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, eg))
    case True{}:
      %Equal.sym(D.Bytes & (D.Bytes & Bool), BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl), (C.BT(sl, st), (C.BT(len, t), Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl))))), SMB.same_pair_t(sl, st, len, t, 0, at, sl)) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.cmp.k(back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, _, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, fneed))
      heq(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, eg, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl))), {==})

def hok2(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>}, +sl: U32, +st: AT.Tree<U32>, +ok: Bool,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {Bool.pick(String, ok, NR.chars(WW.V(sl, st)), TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))))) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.wb(back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, DE.CX(rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), fneed, NX.Wb{C.BT(sl, st), C.BT(len, t), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), ok})):
  match ok:
    case False{}:
      hdec(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk)
    case True{}:
      hcmp(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, U32.is_eq(sl, ((lf + 1 : U32) - at : U32)), {==})

def hwr(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>}, m: TX.WR(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), NX.write(C.BT(len, t), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), at, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))))) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.wb(back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, DE.CX(rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), fneed, NX.write(C.BT(len, t), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), at, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))))):
  (+sl, m1) = m
  (+st, m2) = m1
  (+ok, m3) = m2
  (eqw, m4) = m3
  (okw, pk) = m4
  %Equal.sym(NX.Wb, NX.write(C.BT(len, t), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), at, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), NX.Wb{C.BT(sl, st), C.BT(len, t), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), ok}, eqw) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.wb(back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, DE.CX(rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), fneed, _))
  hok2(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, ok, okw, pk)

def hsame(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>}, +g: Bool, +eg: {Bool.and(Bool.and(Bool.and(U32.is_zero(k), U32.is_zero(tr)), Nat.is_eq(dl, 0n)), up) == g : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.same(g, back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, DE.CX(rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), fneed, C.BT(len, t), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))))):
  match g:
    case True{}:
      hdec(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk)
    case False{}:
      hwr(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, TX.write_t(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e3, e4, e5, e6, e7, lf, PE.REF(e2, e3), Q.TL(als), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))), hok,
        kb1(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), kb2(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), kb3(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

def hnz(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win}, +m: Maybe<&2, Q.K3>, +em: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == m : Maybe<&2, Q.K3>}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.nr(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), fneed, Q.NZB(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), m))):
  match m:
    case None{}:
      hdec(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk)
    case Some{Q.K3{+k, +tr, +dl}}:
      hsame(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, em, Bool.and(Bool.and(Bool.and(U32.is_zero(k), U32.is_zero(tr)), Nat.is_eq(dl, 0n)), up), {==})

def hm(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed)):
  %emk : DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(rest, pd, eof), _, C.BT(len, t), fneed))
  %Equal.sym(NX.Nr, NX.norm(C.BT(len, t), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))), Q.NZB(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))))), TN.norm_pair(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))))) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.nr(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), fneed, _))
  hnz(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))), {==})

def hmir(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool}, m: C.BMirror(NR.of_str(c))) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed)):
  (+cbl, m1) = m
  (+cbt, e) = m1
  hm(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, CA.ah.mk(fa, c, a, b, r, cbl, cbt, hf, Equal.sym(D.Bytes, C.BT(cbl, cbt), NR.of_str(c), e)))

def hit(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed)):
  %Equal.sym(List<&2, NX.Ap>, als, PE.REF(e2, e3) <> Q.TL(als), alsE(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, _, up, DE.CX(rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed))
  hmir(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, C.bmirror(NR.of_str(c)))
