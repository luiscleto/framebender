import Base
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_list.bend as BL
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_nat.bend as NN
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./LAWS.bend as L
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./norm_run.bend as NR
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_ib.bend as IB
import ./proof_b_adv_judge.bend as JG
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_wr.bend as WR
import ./proof_b_alleles.bend as AA
import ./proof_b_alleles_list.bend as AL
import ./proof_b_alleles_loop.bend as ALP
import ./proof_b_cache.bend as CA
import ./proof_b_cache_lem.bend as X
import ./proof_b_cachedefs.bend as CD
import ./proof_b_cut.bend as CU
import ./proof_b_defs.bend as P
import ./proof_b_lines.bend as LN
import ./proof_b_lines_pd.bend as Y
import ./proof_b_lines_str.bend as LSS
import ./proof_b_lit.bend as LT
import ./proof_b_run.bend as PR
import ./proof_b_simdefs.bend as S
import ./proof_fast.bend as PF
import ./proof_window_defs.bend as WS
import ./proof_window_lists.bend as WL
import ./protocol.bend as Pr
import ./run.bend as R
import ./tan.bend as V
import ./types.bend as B
import ./proof_b_cachedefs.bend as PC
import ./proof_b_adv_fast.bend as FA
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_dec.bend as BDe
import ./proof_c_bud.bend as CB
import ./proof_b_budget_mb.bend as BM
import ./proof_b_budget_fl.bend as FL
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The fast path and the budget (generated from proof_b_adv_fast.bend and proof_b_adv_hit.bend: the same
# walk, BD.AdvC in place of S.AdvG, nothing asked, bi carried; leaves: proof_b_budget_mb.bend).

def fhit.w(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(FH.n(pos), 1n), CD.bases_of(D.slice(FH.xs(len, t), FH.n((e2 + 1 : U32)), FH.n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  +hal: {Nat.is_le(FH.n(at), FH.n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(FH.n(lf), FH.n(len)) == True{} : Bool},
  +hfl: {D.first(FH.xs(len, t), FH.n(at), FH.n(len), 10) == FH.n(lf) : Nat},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +i2: {PR.RunInv(rp2) == True{} : Bool},
  +sp2: {P.settle(P.specRun(rp2)) == P.settle(FH.BL0(o, rp1, len, t, at, lf, pos, P.btext(len, t, at, (e0 - at : U32)))) : R.RunSt},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(FH.AofL(len, t, at, lf)) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(FH.AofL(len, t, at, lf)) == True{} : Bool})),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.SB{C.BT(len, t), (lf + 1 : U32)}, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, CD.mkWin(fa, wp), None{}, False{}, dfs}}):
  match sl:
    case (hsp, q):
      match q:
        case (hn, q2):
          (BM.went_done(dfs, fa, cs, o, S.MBP{rp}, S.MBP{rp2}, len, t, d, at, lf, rest, pd, eof, back, 0n, wp, wp, None{}, None{}, fneed, False{}, hsp, hn),
            BM.bi0(fa, wp, None{}, BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, (lf + 1 : U32)}, rest}), P.mkPd(pd), eof, cs)))

def fhit.d(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(FH.n(pos), 1n), CD.bases_of(D.slice(FH.xs(len, t), FH.n((e2 + 1 : U32)), FH.n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +hal: {Nat.is_le(FH.n(at), FH.n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(FH.n(lf), FH.n(len)) == True{} : Bool},
  +hfl: {D.first(FH.xs(len, t), FH.n(at), FH.n(len), 10) == FH.n(lf) : Nat},
  fd: &p2: P.RunP -> ({NR.fast_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), FH.n(pos), C.BT(len, t), at, FH.KK(at, lf)) == (P.mkRun(p2), C.BT(len, t)) : NR.Run & D.Bytes}
  & ({PR.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Normalized{}, FH.n(pos), B.Line.body(Norm.line(FH.AofL(len, t, at, lf))), False{}}, P.specRun(rp1), o, Norm.line(FH.AofL(len, t, at, lf)), B.At{P.RunP.n(rp1), P.btext(len, t, at, (e0 - at : U32)), Nat.show(FH.n(pos))}, FH.n(pos))) : R.RunSt})),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.hit(o, (P.mkRun(rp1), P.RunP.n(rp1)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, CD.mkWin(fa, wp))):
  match fd:
    case (+rp2, q):
      match q:
        case (efd, q2):
          match q2:
            case (i2, sp2):
              %Equal.sym(NR.Run & D.Bytes, NR.fast_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), FH.n(pos), C.BT(len, t), at, FH.KK(at, lf)), (P.mkRun(rp2), C.BT(len, t)), efd) :
                BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.done.b(o, _, (lf + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, CD.mkWin(fa, wp)))
              fhit.w(dfs, fa, T, cs, O, N, o, rp, rp1, rp2, len, t, d, at, rest, pd, eof, back, wp, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c0, a0, b0, r0,
                hw, hr, hg, hx, hin, hok, hs, hp, hse, hf, hc0, hrc, hjt, hal, hlt, hfl, s1, n1, hin1, i2, sp2,
                LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt), hbi)

def fhit.t(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(FH.n(pos), 1n), CD.bases_of(D.slice(FH.xs(len, t), FH.n((e2 + 1 : U32)), FH.n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.hit(o, NR.Run.n(NR.tick(P.mkRun(rp))), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, CD.mkWin(fa, wp))):
  +A = FH.AofL(len, t, at, lf)
  +l = Norm.line(A)
  +chrom = P.btext(len, t, at, (e0 - at : U32))
  +hfl = PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt = PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hjr = FH.j_range(len, t, d, at, lf, hok, hs, Equal.sym(Nat, D.first(FH.xs(len, t), FH.n(at), FH.n(len), 10), FH.n(lf), hfl))
  +hal = W.and_l(Nat.is_le(FH.n(at), FH.n(lf)), Nat.is_le(FH.n(lf), FH.n(len)), hjr)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hc1 = Equal.trans(Maybe<&2, String>, P.RunP.c(rp1), P.RunP.c(rp), Some{chrom}, FH.c_tick(rp, rp1, s1), hcr)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.hit(o, NR.Run.n(_), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, CD.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.hit(o, _, pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, CD.mkWin(fa, wp)))
  fhit.d(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c0, a0, b0, r0, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hp, hse, hcr, hsm, hf, hc0, hrc, hjt, rp1, s1, n1, hin1, hal, hlt, hfl,
    PR.run_fast_done(rp1, o, l, FH.n(pos), chrom, len, t, d, at, FH.KK(at, lf), i1, hin1, hx1, hok,
      FH.k_fit(len, t, d, at, lf, hok, hal, hlt), FH.k_text(len, t, d, at, lf, hok, hs, hfl, hal, hlt), hc1, hbig1,
      FH.k_le_z(len, t, d, at, lf, 268435456, 268435457, hok, hal, hlt, hsm, {==})), hbi)

def fhit(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +c0: String, +a0: Nat, +b0: Nat, +r0: String,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c0) == Some{r0} : Maybe<&2, String>},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c0 : String},
  +hrc: {J.ref_check(String.length(r0), Nat.min(a0, String.length(r0)), B.Bases.of_fasta(CD.letters(r0, a0, b0)), Nat.sub(FH.n(pos), 1n), CD.bases_of(D.slice(FH.xs(len, t), FH.n((e2 + 1 : U32)), FH.n((e3 - e2 - 1 : U32))))) == Some{True{}} : Maybe<&2, Bool>},
  +hjt: {WS.truthful(fa, c0, Some{CD.jtruth(fa, c0, a0, b0)}) == True{} : Bool},
  tk: WR.TKW(rp),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.hit(o, Norm.ticked(P.mkRun(rp)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, CD.mkWin(fa, wp))):
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
                          fhit.t(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c0, a0, b0, r0, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hp, hse, hcr, hsm, hf, hc0, hrc, hjt, rp1, et, i1, s1, n1, obl1, hbi)

def F.need(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{})) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{})) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{})) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hb0: {Nat.is_eq(back, 0n) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{})), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{}), Norm.fast.need(o, Norm.Run.cur(P.mkRun(rp)), back, pos, (e3 - e2 - 1 : U32), C.BT(len, t), at, DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp))):
  %Equal.sym(NR.Run & String, Norm.Run.cur(P.mkRun(rp)), (P.mkRun(rp), Maybe.default(&2, String, P.RunP.c(rp), "")), FA.cur_eq(rp)) :
    BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{}), Norm.fast.need(o, _, back, pos, (e3 - e2 - 1 : U32), C.BT(len, t), at, DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp)))
  %Equal.sym(Maybe<&2, String>, P.RunP.c(rp), Some{P.btext(len, t, at, (e0 - at : U32))}, hcr) :
    BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, False{}), Norm.fast.need(o, (P.mkRun(rp), Maybe.default(&2, String, _, "")), back, pos, (e3 - e2 - 1 : U32), C.BT(len, t), at, DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp)))
  FL.want_c(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp, hse, hb0)

def F.wn(+dfs: B.Defs, +fneed: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hb0: {Nat.is_eq(back, 0n) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), Norm.WNeed{}}, DE.CX(False{}, dfs, rest, pd, eof), fneed)):
  match fneed:
    case True{}:
      BDe.c.dec(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, True{}, hb, hw, hr, hg, hx, hbig, hbi)
    case False{}:
      F.need(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, hb0, hbi)

def F.wo(+dfs: B.Defs, +w: Norm.Wr, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hn: {Norm.Wr.hit(w) == False{} : Bool},
  +hw0: {BD.wr_ok(w, back) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), w}, DE.CX(False{}, dfs, rest, pd, eof), fneed)):
  match w:
    case Norm.WHit{}:
      Empty.absurd(BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), Norm.WHit{}}, DE.CX(False{}, dfs, rest, pd, eof), fneed)), W.ft(Equal.sym(Bool, True{}, False{}, hn)))
    case Norm.WNeed{}:
      F.wn(dfs, fneed, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, hw0, hbi)
    case Norm.WMiss{}:
      BDe.c.dec(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)

def F.kw(+dfs: B.Defs, +w: Norm.Wr, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {Bool.pick(String, Norm.Wr.hit(w), P.btext(len, t, at, (e0 - at : U32)), c) == c : String},
  +hrc: {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w),
      J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat((e3 - e2 - 1 : U32))))),
      Some{True{}}) == Some{True{}} : Maybe<&2, Bool>},
  +eqw: {Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w} : Norm.Wo},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w}, DE.CX(False{}, dfs, rest, pd, eof), fneed)):
  match w:
    case Norm.WHit{}:
      fhit(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c, a, b, r, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hp, hse, hcr, hsm, hf, hc, hrc, CA.jtruth_ok(fa, c, a, b), PR.run_tick(rp, hi), hbi)
    case Norm.WNeed{}:
      F.wo(dfs, Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, FL.kw_b0(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, c, a, b, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hb, W.c9_6(S.md_ok(S.MBP{rp}), W.W1(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W2(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W3(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W4(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W5(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W6(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W7(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W8(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), hw), W.and_r(E.is_bytes(c), Norm.len_le(c, 268435456), W.c9_7(S.md_ok(S.MBP{rp}), W.W1(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W2(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W3(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W4(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W5(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W6(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W7(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), W.W8(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), hw)), hok, hs, hp, hse, eqw, hbi), hbi)
    case Norm.WMiss{}:
      F.wo(dfs, Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, {==}, hbi)

def F.ks(+dfs: B.Defs, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  h: FA.AHW(fa, c, a, b, r, len, t, at, e0, pos, e2, e3),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(False{}, dfs, rest, pd, eof), fneed)):
  match h:
    case (+w, q):
      match q:
        case (+eq, q2):
          match q2:
            case (hc, hrc):
              %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w}, eq) :
                BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(False{}, dfs, rest, pd, eof), fneed))
              F.kw(dfs, w, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, hf, hc, hrc, eq, hbi)

def F.kn(+dfs: B.Defs, +m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +em: {B.Fasta.find(fa, c) == m : Maybe<&2, String>},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(False{}, dfs, rest, pd, eof), fneed)):
  match m:
    case None{}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, False{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, False{}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}}, eq) :
        BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(False{}, dfs, rest, pd, eof), fneed))
      F.wo(dfs, Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, BM.bz_none(back, BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs), AB.subst(Maybe<&2, String>, z => {BN.bi.ls(back, CD.mkWin.k(z, c, a, b, False{}), None{}, BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs)) == True{} : Bool}, B.Fasta.find(fa, c), None{}, em, hbi)), hbi)
    case Some{+r}:
      +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hmw = W.c9_7(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
      +hcb = W.and_l(E.is_bytes(c), Norm.len_le(c, 268435456), hmw)
      +hcl = W.and_r(E.is_bytes(c), Norm.len_le(c, 268435456), hmw)
      F.ks(dfs, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, em,
        CA.against_hit(fa, c, a, b, r, len, t, d, at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32), hb, em, hcb, hcl, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp),
          FH.ref_fit(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp), FH.ref_up(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp),
          PJ.pp_nz(len, t, pos, e0, e1, CU.pass_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), CU.pass_pos_small(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp), FH.ref_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), hbi)

def F.st(+dfs: B.Defs, +m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +em: {B.Fasta.find(fa, c) == m : Maybe<&2, String>},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(False{}, dfs, rest, pd, eof), fneed)):
  match m:
    case None{}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WNeed{}}, eq) :
        BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(False{}, dfs, rest, pd, eof), fneed))
      F.wo(dfs, Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, BM.bz_none(back, BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs), AB.subst(Maybe<&2, String>, z => {BN.bi.ls(back, CD.mkWin.k(z, c, a, b, True{}), None{}, BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs)) == True{} : Bool}, B.Fasta.find(fa, c), None{}, em, hbi)), hbi)
    case Some{+r}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), Norm.WMiss{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WMiss{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WMiss{}}, eq) :
        BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(False{}, dfs, rest, pd, eof), fneed))
      F.wo(dfs, Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, {==}, hbi)

def F.win(+dfs: B.Defs, +wp: CD.WP, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, wp), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(False{}, dfs, rest, pd, eof), fneed)):
  match wp:
    case CD.WPNone{}:
      F.wo(dfs, Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPNone{}, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, BM.bz_none(back, BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs), hbi), hbi)
    case CD.WPUnk{+c}:
      F.wo(dfs, Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPUnk{c}, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, {==}, hbi)
    case CD.WPKnown{+c, +a, +b}:
      F.kn(dfs, B.Fasta.find(fa, c), c, a, b, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, hbi)
    case CD.WPStr{+c, +a, +b}:
      F.st(dfs, B.Fasta.find(fa, c), c, a, b, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==}, hbi)

def F.le(+dfs: B.Defs, +le: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +ele: {U32.is_le((lf - at : U32), 268435456) == le : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run.if(le, back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match le:
    case False{}:
      BDe.c.dec(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)
    case True{}:
      F.win(dfs, wp, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, ele, hbi)

def F.q(+dfs: B.Defs, +q: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hpk: {Bool.pick(Maybe<&2, String>, q, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp)) == P.RunP.c(rp) : Maybe<&2, String>},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run.q(back, o, P.mkRun(rp), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), (C.BT(len, t), q), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match q:
    case False{}:
      BDe.c.dec(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)
    case True{}:
      %Equal.sym(Bool, U32.is_lt(at, e0), True{}, hse) :
        BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run.if(Bool.and(Bool.and(True{}, _), U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed))
      F.le(dfs, U32.is_le((lf - at : U32), 268435456), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse,
        Equal.sym(Maybe<&2, String>, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp), hpk), {==}, hbi)

def F.rs(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  h: FA.RSW(rp, len, t, at, e0),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match h:
    case (+q, r):
      match r:
        case (eqs, hpk):
          %Equal.sym(NR.Run & (D.Bytes & Bool), Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), (P.mkRun(rp), (C.BT(len, t), q)), eqs) :
            BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run(back, o, _, at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed))
          F.q(dfs, q, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hpk, hbi)

def F.r0(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +el: {U32.is_lt(at, e0) == False{} : Bool},
  h: FA.R0W(rp, len, t, at, e0),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match h:
    case (+q, eqs):
      %Equal.sym(NR.Run & (D.Bytes & Bool), Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), (P.mkRun(rp), (C.BT(len, t), q)), eqs) :
        BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run(back, o, _, at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed))
      %Equal.sym(Bool, U32.is_lt(at, e0), False{}, el) :
        BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run.if(Bool.and(Bool.and(q, _), U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed))
      %Equal.sym(Bool, Bool.and(q, False{}), False{}, FA.and_f(q)) :
        BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run.if(Bool.and(_, U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed))
      BDe.c.dec(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)

def F.lt(+dfs: B.Defs, +lt: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +el: {U32.is_lt(at, e0) == lt : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match lt:
    case True{}:
      F.rs(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, el, PR.run_same(rp, len, t, d, at, e0, hi, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), el, FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), hbi)
    case False{}:
      F.r0(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, el, FA.run_same0(rp, len, t, d, at, e0, hi, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), el, FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), hbi)

def F.pre(+dfs: B.Defs, +pr: NF.Pre, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +ep: {CU.pre_of(len, t, at) == pr : NF.Pre},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.pre(back, o, P.mkRun(rp), at, NF.Pr{C.BT(len, t), pr}, DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match pr:
    case NF.Pass{+pos, +e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      F.lt(dfs, U32.is_lt(at, e0), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ep, {==}, hbi)
    case NF.Slow{}:
      CB.fix_bud(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, hbi)
    case NF.Incomplete{}:
      BDe.c.dec(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)

def F.top(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.pre(back, o, P.mkRun(rp), at, NF.line(C.BT(len, t), at), DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +hi = W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
  +hso = LI.srcs_head(rest, len, t, d, at, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  %Equal.sym(NF.Pr, NF.line(C.BT(len, t), at), NF.Pr{C.BT(len, t), CU.pre_of(len, t, at)}, CU.line_pair(len, t, at)) :
    BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fast.pre(back, o, P.mkRun(rp), at, _, DE.CX(False{}, dfs, rest, pd, eof), CD.mkWin(fa, wp), fneed))
  F.pre(dfs, CU.pre_of(len, t, at), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, {==}, hbi)

def c.fast(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.fast.pre(back, o, P.mkRun(rp), at, NF.line(C.BT(len, t), at), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  F.top(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hbi)
