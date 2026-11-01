import Base
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_list.bend as BL
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
import ./proof_b_adv_sp.bend as HX
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
import ./proof_b_skip.bend as SK
import ./proof_b_skip_hit.bend as SKH

# The out-of-scope line's hit and the budget: generated from
# proof_b_budget_fast.bend's fhit.* as proof_b_skip_hit.bend from the fast
# hit (the window's facts dropped, NR.skip_done, Norm.skip.hit).

def bshit.w(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hal: {Nat.is_le(FH.n(at), FH.n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(FH.n(lf), FH.n(len)) == True{} : Bool},
  +hfl: {D.first(FH.xs(len, t), FH.n(at), FH.n(len), 10) == FH.n(lf) : Nat},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +i2: {PR.RunInv(rp2) == True{} : Bool},
  +sp2: {P.settle(P.specRun(rp2)) == P.settle(SKH.BL0s(o, rp1, len, t, at, lf, pos, P.btext(len, t, at, (e0 - at : U32)))) : R.RunSt},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(FH.AofL(len, t, at, lf)) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(FH.AofL(len, t, at, lf)) == True{} : Bool})),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.Src.of(hold, C.BT(len, t), (lf + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, CD.mkWin(fa, wp), None{}, False{}, dfs}}):
  match sl:
    case (hsp, q):
      match q:
        case (hn, q2):
          (BM.went_of(hold, dfs, fa, cs, o, rp, len, t, d, at, lf, rest, pd, eof, back, wp, wp, fneed, P.mkRun(rp2), hsp, hn),
            BM.bi_of(hold, dfs, fa, cs, o, len, t, d, lf, rest, pd, eof, wp, P.mkRun(rp2)))

def bshit.d(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +hal: {Nat.is_le(FH.n(at), FH.n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(FH.n(lf), FH.n(len)) == True{} : Bool},
  +hfl: {D.first(FH.xs(len, t), FH.n(at), FH.n(len), 10) == FH.n(lf) : Nat},
  fd: &p2: P.RunP -> ({NR.skip_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), FH.n(pos), C.BT(len, t), at, FH.KK(at, lf)) == (P.mkRun(p2), C.BT(len, t)) : NR.Run & D.Bytes}
  & ({PR.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Skipped{}, FH.n(pos), B.Line.body(Norm.line(FH.AofL(len, t, at, lf))), False{}}, P.specRun(rp1), o, Norm.line(FH.AofL(len, t, at, lf)), B.At{P.RunP.n(rp1), P.btext(len, t, at, (e0 - at : U32)), Nat.show(FH.n(pos))}, FH.n(pos))) : R.RunSt})),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.skip.hit(o, (P.mkRun(rp1), P.RunP.n(rp1)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
  match fd:
    case (+rp2, q):
      match q:
        case (efd, q2):
          match q2:
            case (i2, sp2):
              %Equal.sym(NR.Run & D.Bytes, NR.skip_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), FH.n(pos), C.BT(len, t), at, FH.KK(at, lf)), (P.mkRun(rp2), C.BT(len, t)), efd) :
                BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.done.b(o, _, (lf + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
              bshit.w(hold, dfs, fa, T, cs, O, N, o, rp, rp1, rp2, len, t, d, at, rest, pd, eof, back, wp, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf,
                hw, hr, hg, hx, hin, hok, hs, hp, hse, hal, hlt, hfl, s1, n1, hin1, i2, sp2,
                LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt), hbi, hnr)

def bshit.t(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.skip.hit(o, NR.Run.n(NR.tick(P.mkRun(rp))), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
  +A = FH.AofL(len, t, at, lf)
  +l = Norm.line(A)
  +chrom = P.btext(len, t, at, (e0 - at : U32))
  +hfl = PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt = PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hjr = FH.j_range(len, t, d, at, lf, hok, hs, Equal.sym(Nat, D.first(FH.xs(len, t), FH.n(at), FH.n(len), 10), FH.n(lf), hfl))
  +hal = W.and_l(Nat.is_le(FH.n(at), FH.n(lf)), Nat.is_le(FH.n(lf), FH.n(len)), hjr)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hc1 = Equal.trans(Maybe<&2, String>, P.RunP.c(rp1), P.RunP.c(rp), Some{chrom}, FH.c_tick(rp, rp1, s1), hcr)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.skip.hit(o, NR.Run.n(_), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.skip.hit(o, _, pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
  bshit.d(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hp, hse, hcr, hsm, rp1, s1, n1, hin1, hal, hlt, hfl,
    PR.run_skip_done(rp1, o, l, FH.n(pos), chrom, len, t, d, at, FH.KK(at, lf), i1, hin1, hx1, hok,
      FH.k_fit(len, t, d, at, lf, hok, hal, hlt), FH.k_text(len, t, d, at, lf, hok, hs, hfl, hal, hlt), hc1, hbig1,
      FH.k_le_z(len, t, d, at, lf, 268435456, 268435457, hok, hal, hlt, hsm, {==})), hbi, hnr)

def bshit(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  tk: WR.TKW(rp),
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.skip.hit(o, Norm.ticked(P.mkRun(rp)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
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
                          bshit.t(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hp, hse, hcr, hsm, rp1, et, i1, s1, n1, obl1, hbi, hnr)

