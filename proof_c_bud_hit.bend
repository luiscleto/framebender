import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_cache.bend as CA
import ./proof_b_enc.bend as EN
import ./proof_b_lines.bend as LN
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_dec.bend as BDe
import ./proof_b_bud_dech.bend as DH
import ./proof_c_defs.bend as Q
import ./proof_c_pre.bend as PE
import ./proof_c_advf.bend as AF
import ./proof_c_tan_pair.bend as TP
import ./proof_c_text.bend as TX
import lawful-bytes@0.1.1.0/defs.bend as D
import ./bytes_enc.bend as E
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_same.bend as SMB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# Phase C: the budget on the rewrite path once the window holds the record
# and REF matches it (norm.bend fix.hit .. fix.tick): every way out is a
# Went that asks nothing (the line written, DH.CW), the String mode
# (to_str, DH.TMC) or the decoded path (BDe.c.dec). The walk is
# proof_c_hit.bend's, without the judge and text facts. Every variable is
# reusable.

# The window mkWin(fa, WPKnown{c, a, b}) unfolds to (CA.ah.mk), with its
# CHROM bytes mirrored as C.BT(cbl, cbt).
def RL(+r: String, +a: Nat, +b: Nat) -> U32:
  U32.from_nat(String.length(CD.letters(r, a, b)))

def RT(+r: String, +a: Nat, +b: Nat) -> AT.Tree<U32>:
  EN.enc_t(CD.letters(r, a, b))

def OFU(+a: Nat, +r: String) -> U32:
  U32.from_nat(Nat.min(a, String.length(r)))

def CLU(+a: Nat, +r: String) -> U32:
  Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)

def WK(+c: String, +cbl: U32, +cbt: AT.Tree<U32>, +a: Nat, +b: Nat, +r: String) -> Norm.Win:
  Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(RL(r, a, b), RT(r, a, b)), OFU(a, r), RL(r, a, b), CLU(a, r)}

# ---------------------------------------------------------------------------
# Line facts
# ---------------------------------------------------------------------------

def ae.k(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  h: {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), PE.REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))) ->
  {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}:
  match h:
    case (eq, r1):
      eq

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
  +hx1 = AB.subst(Nat, z => {Nat.is_le(U32.to_nat(x), z) == True{} : Bool}, Nat.add(U32.to_nat(y), 1n), U32.to_nat((y + 1 : U32)), Equal.sym(Nat, U32.to_nat((y + 1 : U32)), Nat.add(U32.to_nat(y), 1n), hinc),
    N.le_trans(U32.to_nat(x), U32.to_nat(y), Nat.add(U32.to_nat(y), 1n), hxy, N.le_add_r(U32.to_nat(y), 1n)))
  %Equal.sym(Nat, U32.to_nat(((y + 1 : U32) - x : U32)), Nat.sub(U32.to_nat((y + 1 : U32)), U32.to_nat(x)), LP.sub_u((y + 1 : U32), x, hx1)) : {Nat.is_le(Nat.add(U32.to_nat(x), _), U32.to_nat(len)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(U32.to_nat(x), Nat.sub(U32.to_nat((y + 1 : U32)), U32.to_nat(x))), U32.to_nat((y + 1 : U32)), N.le_sub_add(U32.to_nat(x), U32.to_nat((y + 1 : U32)), hx1)) : {Nat.is_le(_, U32.to_nat(len)) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat((y + 1 : U32)), Nat.add(U32.to_nat(y), 1n), hinc) : {Nat.is_le(_, U32.to_nat(len)) == True{} : Bool}
  C.succ_le(U32.to_nat(y), U32.to_nat(len), hy)

def hdec(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r), fneed)):
  %Equal.sym(Norm.Win, WK(c, cbl, cbt, a, b, r), CD.mkWin(fa, CD.WPKnown{c, a, b}), emk) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, DE.CX(hold, dfs, rest, pd, eof), _, fneed))
  BDe.c.dec(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hnr)

def hcw(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  x: NR.Run,
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.Went{Norm.St{o, Norm.MB{x}, Con{Norm.Src.of(hold, C.BT(len, t), (lf + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, WK(c, cbl, cbt, a, b, r), None{}, False{}, dfs}}):
  match sl:
    case (hsp, q):
      match q:
        case (hn, q2):
        %Equal.sym(Norm.Win, WK(c, cbl, cbt, a, b, r), CD.mkWin(fa, CD.WPKnown{c, a, b}), emk) :
          BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.Went{Norm.St{o, Norm.MB{x}, Con{Norm.Src.of(hold, C.BT(len, t), (lf + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, _, None{}, False{}, dfs}})
        DH.CW(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, lf, hsp, hn, x, hnr)

def fout(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  X: NR.Run & D.Bytes,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.out(o, X, lf, C.BT(len, t), DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r))):
  match X:
    case (x, sc):
      hcw(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, x, LN.src_line(len, t, d, at, lf, hok, hs, PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), hnr)

def ftick(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  p: NR.Run & Nat, +q: Nat, +sl: U32, +st: AT.Tree<U32>, +m: U32,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.tick(o, p, q, pos, lf, C.BT(len, t), C.BT(sl, st), m, DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r))):
  match p:
    case (x, +k):
      fout(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, NR.fix_done(x, R.Opts.w(o), k, q, U32.to_nat(pos), C.BT(sl, st), m), hnr)

def hts(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.to_str(o, P.mkRun(rp), C.BT(len, t), at, back, DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r), False{})):
  %Equal.sym(Norm.Win, WK(c, cbl, cbt, a, b, r), CD.mkWin(fa, CD.WPKnown{c, a, b}), emk) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.to_str(o, P.mkRun(rp), C.BT(len, t), at, back, DE.CX(hold, dfs, rest, pd, eof), _, False{}))
  DH.TMC(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, False{}, hnr)

def hfits(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +f: Bool, +q: Nat, +sl: U32, +st: AT.Tree<U32>,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.fits(f, back, o, P.mkRun(rp), q, pos, at, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r))):
  match f:
    case True{}:
      ftick(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, Norm.ticked(P.mkRun(rp)), q, sl, st, sl, hnr)
    case False{}:
      hts(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, hnr)

def hlen(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +q: Nat, +sl: U32, +st: AT.Tree<U32>,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.ne(False{}, back, o, P.mkRun(rp), q, pos, at, lf, C.BT(sl, st), C.BT(len, t), DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r), fneed)):
  %Equal.sym(NR.Run & U32, Norm.Run.oblen(P.mkRun(rp)), (P.mkRun(rp), P.RunP.obl(rp)), SLW.oblen_eq(rp)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.len(back, o, _, q, pos, at, lf, C.BT(len, t), BY.len(C.BT(sl, st)), DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r)))
  hfits(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)), q, sl, st, hnr)

def hne(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +e: Bool, +q: Nat, +sl: U32, +st: AT.Tree<U32>,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.ne(e, back, o, P.mkRun(rp), q, pos, at, lf, C.BT(sl, st), C.BT(len, t), DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r), fneed)):
  match e:
    case True{}:
      hdec(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, hnr)
    case False{}:
      hlen(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, q, sl, st, hnr)

def hcmp(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +g: Bool, +q: Nat, +sl: U32, +st: AT.Tree<U32>,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.cmp.k(back, o, P.mkRun(rp), q, pos, at, lf, Norm.fix.cmp.if(g, C.BT(sl, st), C.BT(len, t), at, sl), DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r), fneed)):
  match g:
    case False{}:
      hlen(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, q, sl, st, hnr)
    case True{}:
      %Equal.sym(D.Bytes & (D.Bytes & Bool), BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl), (C.BT(sl, st), (C.BT(len, t), Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl))))), SMB.same_pair_t(sl, st, len, t, 0, at, sl)) :
        BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.cmp.k(back, o, P.mkRun(rp), q, pos, at, lf, _, DE.CX(hold, dfs, rest, pd, eof), WK(c, cbl, cbt, a, b, r), fneed))
      hne(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), at, sl))), q, sl, st, hnr)

def hok2(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +ok: Bool, +q: Nat, +sl: U32, +st: AT.Tree<U32>,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.wb(back, o, P.mkRun(rp), q, pos, at, lf, DE.CX(hold, dfs, rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), OFU(a, r), RL(r, a, b), CLU(a, r), fneed, NX.Wb{C.BT(sl, st), C.BT(len, t), C.BT(RL(r, a, b), RT(r, a, b)), ok})):
  match ok:
    case False{}:
      hdec(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, hnr)
    case True{}:
      hcmp(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, U32.is_eq(sl, ((lf + 1 : U32) - at : U32)), q, sl, st, hnr)

def hwr(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat, m: TX.WR(len, t, RL(r, a, b), RT(r, a, b), NX.write(C.BT(len, t), C.BT(RL(r, a, b), RT(r, a, b)), at, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, pos, OFU(a, r)), TX.TXT(len, t, d, RL(r, a, b), RT(r, a, b), at, e0, e1, e2, e4, lf, TX.QQ(pos, k, dl), TX.ALA(len, t, RL(r, a, b), RT(r, a, b), PE.REF(e2, e3), k, tr, dl, pos, OFU(a, r)), TX.ACC(Q.TL(als), "", True{}, len, t, RL(r, a, b), RT(r, a, b), k, tr, dl, pos, OFU(a, r)))),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.wb(back, o, P.mkRun(rp), TX.QQ(pos, k, dl), pos, at, lf, DE.CX(hold, dfs, rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), OFU(a, r), RL(r, a, b), CLU(a, r), fneed, NX.write(C.BT(len, t), C.BT(RL(r, a, b), RT(r, a, b)), at, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, pos, OFU(a, r)))):
  match m:
    case (+sl, m1):
      match m1:
        case (+st, m2):
          match m2:
            case (+ok, m3):
              match m3:
                case (eqw, m4):
                  %Equal.sym(NX.Wb, NX.write(C.BT(len, t), C.BT(RL(r, a, b), RT(r, a, b)), at, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, pos, OFU(a, r)), NX.Wb{C.BT(sl, st), C.BT(len, t), C.BT(RL(r, a, b), RT(r, a, b)), ok}, eqw) :
                    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.wb(back, o, P.mkRun(rp), TX.QQ(pos, k, dl), pos, at, lf, DE.CX(hold, dfs, rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), OFU(a, r), RL(r, a, b), CLU(a, r), fneed, _))
                  hok2(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, ok, TX.QQ(pos, k, dl), sl, st, hnr)

def hsame(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +g: Bool, +k: U32, +tr: U32, +dl: Nat,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.same(g, back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), k, tr, dl, DE.CX(hold, dfs, rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), OFU(a, r), RL(r, a, b), CLU(a, r), fneed, C.BT(len, t), C.BT(RL(r, a, b), RT(r, a, b)))):
  match g:
    case True{}:
      hdec(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, hnr)
    case False{}:
      hwr(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, k, tr, dl, TX.write_t(len, t, d, RL(r, a, b), RT(r, a, b), at, e0, e1, e2, e3, e4, e5, e6, e7, lf, PE.REF(e2, e3), Q.TL(als), k, tr, dl, pos, OFU(a, r), hok,
        kbg(len, t, d, at, e0, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_le_trans(U32.to_nat(e0), U32.to_nat(e4), U32.to_nat(len), N.lt_trans(U32.to_nat(e0), U32.to_nat(e1), U32.to_nat(e4), PJ.lf_01(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e1), U32.to_nat(e2), U32.to_nat(e4), PJ.lf_12(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e2), U32.to_nat(e3), U32.to_nat(e4), PJ.lf_23(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_34(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))), AF.e4le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))),
        kbg(len, t, d, e1, e2, hok, N.lt_to_le(U32.to_nat(e1), U32.to_nat(e2), PJ.lf_12(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), N.lt_le_trans(U32.to_nat(e2), U32.to_nat(e4), U32.to_nat(len), N.lt_trans(U32.to_nat(e2), U32.to_nat(e3), U32.to_nat(e4), PJ.lf_23(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_34(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), AF.e4le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))),
        kbg(len, t, d, e4, lf, hok, N.lt_to_le(U32.to_nat(e4), U32.to_nat(lf), N.lt_le_trans(U32.to_nat(e4), U32.to_nat(e7), U32.to_nat(lf), N.lt_trans(U32.to_nat(e4), U32.to_nat(e5), U32.to_nat(e7), PJ.lf_45(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e5), U32.to_nat(e6), U32.to_nat(e7), PJ.lf_56(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_67(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))), PJ.lf_7l(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))), PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))), hnr)

def hnz(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +m: Maybe<&2, Q.K3>,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.nr(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(hold, dfs, rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), OFU(a, r), RL(r, a, b), CLU(a, r), fneed, Q.NZB(len, t, RL(r, a, b), RT(r, a, b), m))):
  match m:
    case None{}:
      hdec(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, hnr)
    case Some{Q.K3{+k, +tr, +dl}}:
      hsame(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, Bool.and(Bool.and(Bool.and(U32.is_zero(k), U32.is_zero(tr)), Nat.is_eq(dl, 0n)), up), k, tr, dl, hnr)

def hm(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {WK(c, cbl, cbt, a, b, r) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(hold, dfs, rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed)):
  %emk : BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(hold, dfs, rest, pd, eof), _, C.BT(len, t), fneed))
  %Equal.sym(NX.Nr, NX.norm(C.BT(len, t), C.BT(RL(r, a, b), RT(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, OFU(a, r)), Q.NZB(len, t, RL(r, a, b), RT(r, a, b), Q.NZ(len, t, RL(r, a, b), RT(r, a, b), PE.REF(e2, e3) <> Q.TL(als), pos, OFU(a, r))), TP.norm_pair_t(len, t, RL(r, a, b), RT(r, a, b), PE.REF(e2, e3) <> Q.TL(als), pos, OFU(a, r))) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.nr(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(hold, dfs, rest, pd, eof), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), OFU(a, r), RL(r, a, b), CLU(a, r), fneed, _))
  hnz(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, emk, Q.NZ(len, t, RL(r, a, b), RT(r, a, b), PE.REF(e2, e3) <> Q.TL(als), pos, OFU(a, r)), hnr)

def hmir(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  m: C.BMirror(NR.of_str(c)),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, PE.REF(e2, e3) <> Q.TL(als), up, DE.CX(hold, dfs, rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed)):
  match m:
    case (+cbl, m1):
      match m1:
        case (+cbt, e):
          hm(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, cbl, cbt, CA.ah.mk(fa, c, a, b, r, cbl, cbt, hf, Equal.sym(D.Bytes, C.BT(cbl, cbt), NR.of_str(c), e)), hnr)

def hit(+hold: Bool, +dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, DE.CX(hold, dfs, rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed)):
  %Equal.sym(List<&2, NX.Ap>, als, PE.REF(e2, e3) <> Q.TL(als), alsE(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.hit(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, _, up, DE.CX(hold, dfs, rest, pd, eof), CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), fneed))
  hmir(hold, dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf, C.bmirror(NR.of_str(c)), hnr)
