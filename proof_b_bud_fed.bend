import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DD
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_b_drive_chunk.bend as CH
import ./proof_b_cache.bend as PCA
import ./proof_b_bud_start.bend as BSt
import ./proof_run_base.bend as RB
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_lem.bend as BL
import ./proof_b_adv_wf.bend as W
import ./proof_b_enc.bend as EN
import ./proof_b_lines.bend as PL
import ./proof_b_lines_str.bend as LS
import ./proof_b_lines_pd.bend as LP
import ./proof_b_run.bend as RN
import ./proof_base.bend as PB
import ./proof_machine_nat.bend as PN
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as FD
import lawful-bytes@0.1.0.0/proof_list.bend as Q
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-bytes@0.1.0.0/proof_grow.bend as G
import ./proof_b_lines_lst.bend as LT
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The budget's F1 chunk_fed and F2 eof_fed (notes/bytes_proofs_budget.md;
# statements as in proof_b_budget_step.bend): the state a piece or the end of
# the file is fed into is some good picture q, standing for the report, with
# the guard and nothing asked, whose text still to come has the same lines;
# back, the window, fneed and the mode are kept, so WA is the same and bi
# holds again. The proofs follow the drive area's (proof_b_drive_chunk.bend,
# pb-lines'; proof_b_drive_step.bend's eof chain) with FedG in place of go.

# Same lines, same WA and bi
# ==========================

law le_eq:
  for +a: Nat
  for +b: Nat
  for +e: {a == b : Nat}
  {Nat.is_le(a, b) == True{} : Bool}

def le_eq(a, b, e):
  %Equal.sym(Nat, a, b, e) : {Nat.is_le(_, b) == True{} : Bool}
  N.le_refl(b)

law lines_eq:
  for +dfs: B.Defs
  for +cs2: List<&2, String>
  for +cs: List<&2, String>
  for +o: B.Opts
  for +md: S.MdP
  for +src2: List<&2, P.SrcP>
  for +pd2: P.PdP
  for +eof2: Bool
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hl: {B.Text.lines(S.intext(S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed, dfs}, cs2)) == B.Text.lines(S.intext(S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs}, cs)) : List<&2, B.Line>}
  for +hn2: {S.no_recs(src2) == True{} : Bool}
  for +hn0: {S.no_recs(src) == True{} : Bool}
  {BN.ALL(P.mkSrcs(src2), P.mkPd(pd2), eof2, cs2) == BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) : List<&2, B.Line>}

def lines_eq(dfs,cs2, cs, o, md, src2, pd2, eof2, src, pd, eof, back, wp, fneed, hl, hn2, hn0):
  +Q2 = {S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed, dfs} : S.StP}
  +Q0 = {S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs} : S.StP}
  +A2 = String.append(BN.srcT(P.mkSrcs(src2)), String.append(BN.pdT(P.mkPd(pd2)), S.concat_if(eof2, cs2)))
  +A0 = String.append(BN.srcT(P.mkSrcs(src)), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs)))
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd2), eof2, cs2)
  +L0 = BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +el = Equal.trans(List<&2, B.Line>, B.Text.lines(A2), B.Text.lines(S.intext(Q2, cs2)), B.Text.lines(A0),
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), A2, S.intext(Q2, cs2), BL.text_pic(Q2, cs2, W.nr_first(src2, hn2))),
    Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(Q2, cs2)), B.Text.lines(S.intext(Q0, cs)), B.Text.lines(A0), hl,
      Equal.sym(List<&2, B.Line>, B.Text.lines(A0), B.Text.lines(S.intext(Q0, cs)),
        Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), A0, S.intext(Q0, cs), BL.text_pic(Q0, cs, W.nr_first(src, hn0))))))
  Equal.trans(List<&2, B.Line>, BN.ALL(P.mkSrcs(src2), P.mkPd(pd2), eof2, cs2), L2, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs), BL.all_nr(src2, pd2, eof2, cs2, hn2),
    Equal.trans(List<&2, B.Line>, L2, L0, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs), el, Equal.sym(List<&2, B.Line>, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs), L0, BL.all_nr(src, pd, eof, cs, hn0))))

# A fed state that is the picture Q1 of Q0 with other sources, line end and
# eof, whose text has the same lines.
law fed_leaf:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +cs2: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +src2: List<&2, P.SrcP>
  for +pd2: P.PdP
  for +eof2: Bool
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hw1: {S.WF(fa, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hr1: {S.report(fa, cs2, O, N, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs}), cs) == True{} : Bool}
  for +hla: {BN.ALL(P.mkSrcs(src2), P.mkPd(pd2), eof2, cs2) == BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) : List<&2, B.Line>}
  BD.FedG(fa, T, cs2, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs}), S.mkSt(fa, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed, dfs}))

def fed_leaf(dfs,fa, T, cs, cs2, O, N, o, md, src, pd, eof, src2, pd2, eof2, back, wp, fneed, hw1, hr1, hg, hbi, hla):
  +L2 = BN.ALL(P.mkSrcs(src2), P.mkPd(pd2), eof2, cs2)
  +L0 = BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +leq = hla
  +fl = BN.fast_left(S.mkMd(md), fneed)
  (S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed, dfs}, ({==}, (hw1, (hr1, (hg, ({==},
    (le_eq(BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), None{}, L2), BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), None{}, L0),
       Equal.cong(List<&2, B.Line>, Nat, z => BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), None{}, z), L2, L0, leq)),
     Equal.trans(Bool, BN.bi.ls(back, PC.mkWin(fa, wp), None{}, L2), BN.bi.ls(back, PC.mkWin(fa, wp), None{}, L0), True{},
       Equal.cong(List<&2, B.Line>, Bool, z => BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z), L2, L0, leq), hbi))))))))

# F1: the piece (proof_b_drive_chunk.bend's chain, ending in FedG)
# ==========================================================

# The line end is empty: the piece is the only source.
def ch_empty(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>},
  +he: {String.is_empty(P.pdtext(pd)) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.SB{CH.BTc(c), 0}]), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs}):
  ?TODO


# No LF in the piece: it goes to the line end.
def ch_all3(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +pp2: P.PdP,
  +e2: {Norm.pend.add(P.mkPd(pd), CH.BTc(c), 0, CH.L0(c)) == P.mkPd(pp2) : Norm.Pd},
  +hpo: {P.pd_ok(pp2) == True{} : Bool},
  +hpt: {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c))) : String},
  +hnc: {P.nolf(c) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), CH.BTc(c), 0, CH.L0(c)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs}):
  ?TODO


def ch_all2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>},
  +hnc: {P.nolf(c) == True{} : Bool},
  r: &pp2: P.PdP -> ({Norm.pend.add(P.mkPd(pd), C.BT(CH.L0(c), CH.ET(c)), 0, CH.L0(c)) == P.mkPd(pp2) : Norm.Pd}
    & ({P.pd_ok(pp2) == True{} : Bool}
    & {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c))) : String}))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), CH.BTc(c), 0, CH.L0(c)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs}):
  (+pp2, r1) = r
  (+e2, r2) = r1
  (hpo, hpt) = r2
  ch_all3(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, pp2, e2, hpo, hpt, hnc)

# The piece's LF at j joins the line end.
def ch_join3(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32, +pp2: P.PdP, +pp0: P.PdP,
  +ej: {Norm.join.k(P.mkPd(pd), CH.BTc(c), j) == (P.mkPd(pp2), CH.BTc(c)) : Norm.Pd & D.Bytes},
  +esrc: {Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(PL.pdsrc(pp2)) : Norm.Src},
  +hso: {P.src_ok(PL.pdsrc(pp2)) == True{} : Bool},
  +hst: {P.srctext(PL.pdsrc(pp2)) == String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, (j + 1 : U32))) : String},
  +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp0) : Norm.Pd},
  +hpo0: {P.pd_ok(pp0) == True{} : Bool},
  +hpt0: {P.pdtext(pp0) == "" : String},
  +hlf2: {P.btext(CH.L0(c), CH.ET(c), 0, (j + 1 : U32)) == String.append(P.btext(CH.L0(c), CH.ET(c), 0, j), "\n") : String},
  +hc2: {c == String.append(P.btext(CH.L0(c), CH.ET(c), 0, j), String.append("\n", P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), (j + 1 : U32)}))) : String},
  +hj1: {U32.is_le((j + 1 : U32), CH.L0(c)) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), CH.BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  ?TODO


def ch_join2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +hlf2: {P.btext(CH.L0(c), CH.ET(c), 0, (j + 1 : U32)) == String.append(P.btext(CH.L0(c), CH.ET(c), 0, j), "\n") : String},
  +hc2: {c == String.append(P.btext(CH.L0(c), CH.ET(c), 0, j), String.append("\n", P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), (j + 1 : U32)}))) : String},
  +hj1: {U32.is_le((j + 1 : U32), CH.L0(c)) == True{} : Bool},
  r: &pp2: P.PdP -> ({Norm.join.k(P.mkPd(pd), C.BT(CH.L0(c), CH.ET(c)), j) == (P.mkPd(pp2), C.BT(CH.L0(c), CH.ET(c))) : Norm.Pd & D.Bytes}
    & ({Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(PL.pdsrc(pp2)) : Norm.Src}
    & ({P.src_ok(PL.pdsrc(pp2)) == True{} : Bool}
    & {P.srctext(PL.pdsrc(pp2)) == String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, (j + 1 : U32))) : String}))),
  pe: &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd}
    & ({P.pd_ok(pp) == True{} : Bool}
    & {P.pdtext(pp) == "" : String}))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), CH.BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  (+pp2, r1) = r
  (+ej, r2) = r1
  (+esrc, r3) = r2
  (hso, hst) = r3
  (+pp0, pe1) = pe
  (+f1, pe2) = pe1
  (hpo0, hpt0) = pe2
  ch_join3(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, pp2, pp0, ej, esrc, hso, hst, f1, hpo0, hpt0, hlf2, hc2, hj1)

def ch_join(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +hk: {Nat.is_lt(U32.to_nat(j), U32.to_nat(CH.L0(c))) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(CH.BTc(c)), U32.to_nat(j)) == Some{10} : Maybe<&2, U32>},
  sl: {P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), 0}) == String.append(P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32)), String.append("\n", P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), (j + 1 : U32)}))) : String}
  & ({P.nolf(P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32))) == True{} : Bool}
  & ({U32.is_le((j + 1 : U32), CH.L0(c)) == True{} : Bool}
  & {E.is_bytes(P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32))) == True{} : Bool}))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), CH.BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  ?TODO


# After the piece's first LF search.
def ch_z(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32, +z: Bool,
  +ez: {U32.is_eq(j, CH.L0(c)) == z : Bool},
  +hf: {U32.to_nat(j) == D.first(D.view(CH.BTc(c)), U32.to_nat(0), U32.to_nat(CH.L0(c)), 10) : Nat}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.lf(z, o, S.mkMd(md), CH.BTc(c), j, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  ?TODO


def ch_lf2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +e1: {NF.lf(CH.BTc(c), 0) == NF.Tb{CH.BTc(c), j, U32.is_eq(j, CH.L0(c)), False{}} : NF.Tb},
  +hf: {U32.to_nat(j) == D.first(D.view(CH.BTc(c)), U32.to_nat(0), U32.to_nat(CH.L0(c)), 10) : Nat}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.find(o, S.mkMd(md), NF.lf(CH.BTc(c), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  %Equal.sym(NF.Tb, NF.lf(CH.BTc(c), 0), NF.Tb{CH.BTc(c), j, U32.is_eq(j, CH.L0(c)), False{}}, e1) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.find(o, S.mkMd(md), _, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))
  ch_z(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, U32.is_eq(j, CH.L0(c)), {==}, hf)

def ch_lf(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>},
  r: &j: U32 -> ({NF.lf(C.BT(CH.L0(c), CH.ET(c)), 0) == NF.Tb{C.BT(CH.L0(c), CH.ET(c)), j, U32.is_eq(j, CH.L0(c)), False{}} : NF.Tb}
    & {PL.n(j) == D.first(PL.xs(CH.L0(c), CH.ET(c)), PL.n(0), PL.n(CH.L0(c)), 10) : Nat})) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.find(o, S.mkMd(md), NF.lf(CH.BTc(c), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  (+j, r1) = r
  (e1, hf) = r1
  ch_lf2(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, e1, hf)

def core_if(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +z: Bool,
  +ez: {Nat.is_eq(String.length(P.pdtext(pd)), 0n) == z : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.if(z, o, S.mkMd(md), Nil{}, CH.BTc(c), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match z:
    case True{}:
      ch_empty(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, DS.empty_of_len(P.pdtext(pd), ez))
    case False{}:
      ch_lf(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, PL.lf_ok(CH.L0(c), CH.ET(c), CH.DD(c), 0, hok, LP.u32_le0(CH.L0(c))))

def core(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  ?TODO


# The run gets room for the piece
# ===============================

def chunk_mb2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(CH.L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(CH.L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>},
  +e: {NR.reserve(P.mkRun(rp), CH.L0(c)) == P.mkRun(rp2) : NR.Run},
  +hi2: {RN.RunInv(rp2) == True{} : Bool},
  +hs: {P.specRun(rp2) == P.specRun(rp) : R.RunSt}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), CH.L0(c))}, Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  ?TODO


def chunk_mb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(CH.L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(CH.L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>},
  r: &p2: P.RunP -> ({NR.reserve(P.mkRun(rp), CH.L0(c)) == P.mkRun(p2) : NR.Run}
    & ({RN.RunInv(p2) == True{} : Bool}
    & ({P.specRun(p2) == P.specRun(rp) : R.RunSt}
    & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32})))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), CH.L0(c))}, Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  (+rp2, r1) = r
  (+e, r2) = r1
  (+hi2, r3) = r2
  (hs, ho) = r3
  chunk_mb2(dfs, fa, T, c, cs, O, N, o, rp, rp2, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, e, hi2, hs)

# By the run's mode (the String mode's run has no buffer).
def chunk_md(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(CH.L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(CH.L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), C.BT(CH.L0(c), EN.enc_t(c)))):
  ?TODO


# The piece's facts from the enc area.
def chunk_enc(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool},
  r: {D.ok(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), C.BT(CH.L0(c), EN.enc_t(c)))):
  (hok, r1) = r
  (hv, r2) = r1
  chunk_md(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv)

# step_chunk with the eof flag (DO.StepG2; every state here is before the
# end of the file), for the assembly's sg_chunk.
# F1: a piece of the file fed to a state waiting for more.
def chunk_fed(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DD.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), c <> cs) == True{} : Bool},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, p), Norm.feed(S.mkSt(fa, p), E.enc(c))):
  match p:
    case S.StP{+o, +md, Con{+x, +t}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, t}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), E.enc(c))),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), E.enc(c))),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd(BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), E.enc(c))),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      +hw = DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm)
      %Equal.sym(D.Bytes, E.enc(c), C.BT(CH.L0(c), EN.enc_t(c)), EN.enc_bt(c)) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), _))
      chunk_enc(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, EN.enc_ok(c, hcb, hcn))

# F2: the end of the file (proof_b_drive_step.bend's eof chain, ending in FedG)
# ======================================================================

law eof_empty:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Nil{}) == True{} : Bool}
  for +he: {String.is_empty(P.pdtext(pd)) == True{} : Bool}
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), S.mkSt(fa, S.StP{o, md, Nil{}, pd, True{}, back, wp, None{}, fneed, dfs}))

def eof_empty(dfs,fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, he):
  ?TODO


law eof_full2:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +sp: P.SrcP
  for +pp0: P.PdP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Nil{}) == True{} : Bool}
  for +hne: {String.is_empty(P.pdtext(pd)) == False{} : Bool}
  for +e1: {Norm.eof_src(P.mkPd(pd)) == P.mkSrc(sp) : Norm.Src}
  for +hso: {P.src_ok(sp) == True{} : Bool}
  for +hst: {P.srctext(sp) == String.append(P.pdtext(pd), "\n") : String}
  for +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp0) : Norm.Pd}
  for +hpo: {P.pd_ok(pp0) == True{} : Bool}
  for +hpt: {P.pdtext(pp0) == "" : String}
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.eof_src(P.mkPd(pd))]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs})

def eof_full2(dfs,fa, T, O, N, o, md, pd, back, wp, fneed, sp, pp0, hb, hw, hr, hg, hbi, hne, e1, hso, hst, f1, hpo, hpt):
  ?TODO


law eof_full:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Nil{}) == True{} : Bool}
  for +hne: {String.is_empty(P.pdtext(pd)) == False{} : Bool}
  for eo: &sp: P.SrcP -> ({Norm.eof_src(P.mkPd(pd)) == P.mkSrc(sp) : Norm.Src} & ({P.src_ok(sp) == True{} : Bool} & {P.srctext(sp) == String.append(P.pdtext(pd), "\n") : String}))
  for pe: &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd} & ({P.pd_ok(pp) == True{} : Bool} & {P.pdtext(pp) == "" : String}))
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.eof_src(P.mkPd(pd))]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs})

def eof_full(dfs,fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hne, eo, pe):
  (+sp, eo1) = eo
  (+e1, eo2) = eo1
  (hso, hst) = eo2
  (+pp0, pe1) = pe
  (+f1, pe2) = pe1
  (hpo, hpt) = pe2
  eof_full2(dfs, fa, T, O, N, o, md, pd, back, wp, fneed, sp, pp0, hb, hw, hr, hg, hbi, hne, e1, hso, hst, f1, hpo, hpt)

law eof_if:
  for +dfs: B.Defs
  for +c: Bool
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Nil{}) == True{} : Bool}
  for +hc: {Nat.is_eq(String.length(P.pdtext(pd)), 0n) == c : Bool}
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed_eof.if(c, o, S.mkMd(md), Nil{}, P.mkPd(pd), back, PC.mkWin(fa, wp), None{}, fneed, dfs))

def eof_if(dfs,c, fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hc):
  ?TODO


# F2: the end of the file fed to a state waiting for more.
law eof_fed:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DD.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, p), Nil{}) == True{} : Bool}
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, p), Norm.feed_eof(S.mkSt(fa, p)))

def eof_fed(fa, T, O, N, p, hb, hm, hr, hg, hbi):
  ?TODO



# F3: the answers to a pending Ask
# ================================

# A known window made from Some{r} (pb-cache's hwk, proof_b_bud_win.bend).
def hwk(+c0: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32, +c: String, +a: Nat, +b: Nat) ->
  {BN.holdsW(Norm.win_of.k(c0, a0, b0, clen, off, r), c, a, b) == Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen))) : Bool}:
  match r:
    case (raw, rl):
      {==}

def min_mono(+x: Nat, +y: Nat, +n: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.min(x, n), Nat.min(y, n)) == True{} : Bool}:
  match x y n:
    case 0n _ _:
      N.le_zero_l(Nat.min(y, n))
    case 1n+x1 0n _:
      Empty.absurd({Nat.is_le(Nat.min(1n+x1, n), 0n) == True{} : Bool}, PB.false_ne_true(h))
    case 1n+x1 1n+y1 0n:
      {==}
    case 1n+x1 1n+y1 1n+n1:
      min_mono(x1, y1, n1, h)

def and3(+x: Bool, +y: Bool, +z: Bool, +hx: {x == True{} : Bool}, +hy: {y == True{} : Bool}, +hz: {z == True{} : Bool}) ->
  {Bool.and(Bool.and(x, y), z) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, hx) : {Bool.and(Bool.and(_, y), z) == True{} : Bool}
  %Equal.sym(Bool, y, True{}, hy) : {Bool.and(Bool.and(True{}, _), z) == True{} : Bool}
  %Equal.sym(Bool, z, True{}, hz) : {Bool.and(Bool.and(True{}, True{}), _) == True{} : Bool}
  {==}

def hk(+r: String, +c: String, +a: Nat, +b: Nat, +str: Bool, +c1: String, +a1: Nat, +b1: Nat,
  +hc: {String.eq(c, c1) == True{} : Bool}, +ha: {Nat.is_le(a, a1) == True{} : Bool}, +hb: {Nat.is_le(b1, b) == True{} : Bool}) ->
  {BN.holdsW(PC.mkWin.k(Some{r}, c, a, b, str), c1, a1, b1) == True{} : Bool}:
  match str:
    case False{}:
      +HW = BN.holdsW(Norm.win_of.k(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(PC.letters(r, a, b)))), c1, a1, b1)
      +X0 = Bool.and(Bool.and(String.eq(c, c1), Nat.is_le(a, a1)), Nat.is_le(Nat.min(b1, String.length(r)), Nat.min(b, String.length(r))))
      Equal.trans(Bool, HW, X0, True{}, hwk(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(PC.letters(r, a, b))), c1, a1, b1),
        and3(String.eq(c, c1), Nat.is_le(a, a1), Nat.is_le(Nat.min(b1, String.length(r)), Nat.min(b, String.length(r))), hc, ha, min_mono(b1, b, String.length(r), hb)))
    case True{}:
      and3(String.eq(c, c1), Nat.is_le(a, a1), Nat.is_le(Nat.min(b1, String.length(r)), Nat.min(b, String.length(r))), hc, ha, min_mono(b1, b, String.length(r), hb))

def wh2(+fa: List<&2, B.Contig>, +g: Bool, +r: String, +c: String, +a: Nat, +b: Nat, +c1: String, +a1: Nat, +b1: Nat,
  +hm: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {String.eq(c, c1) == True{} : Bool}, +ha: {Nat.is_le(a, a1) == True{} : Bool}, +hb: {Nat.is_le(b1, b) == True{} : Bool}) ->
  {BN.holdsW(PC.mkWin(fa, Bool.pick(PC.WP, g, PC.WPKnown{c, a, b}, PC.WPStr{c, a, b})), c1, a1, b1) == True{} : Bool}:
  match g:
    case True{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) : {BN.holdsW(PC.mkWin.k(_, c, a, b, False{}), c1, a1, b1) == True{} : Bool}
      hk(r, c, a, b, False{}, c1, a1, b1, hc, ha, hb)
    case False{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) : {BN.holdsW(PC.mkWin.k(_, c, a, b, True{}), c1, a1, b1) == True{} : Bool}
      hk(r, c, a, b, True{}, c1, a1, b1, hc, ha, hb)

def wh(+fa: List<&2, B.Contig>, +m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +c1: String, +a1: Nat, +b1: Nat,
  +hm: {B.Fasta.find(fa, c) == m : Maybe<&2, String>},
  +hc: {String.eq(c, c1) == True{} : Bool}, +ha: {Nat.is_le(a, a1) == True{} : Bool}, +hb: {Nat.is_le(b1, b) == True{} : Bool}) ->
  {BN.holdsW(PC.mkWin(fa, PC.wpOf.k(m, c, a, b)), c1, a1, b1) == True{} : Bool}:
  match m:
    case None{}:
      hc
    case Some{+r}:
      wh2(fa, Norm.le31(Nat.sub(b, a)), r, c, a, b, c1, a1, b1, hm, hc, ha, hb)

# What the pending Ask's window covers, the window set_win builds from its
# answers holds.
def cov_hold(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>, +c1: String, +a1: Nat, +b1: Nat,
  +h: {BN.coversA(Some{Pr.Req{c, a, b} <> t}, c1, a1, b1) == True{} : Bool}) ->
  {BN.holdsW(PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), c1, a1, b1) == True{} : Bool}:
  +X = Bool.and(String.eq(c, c1), Nat.is_le(a, a1))
  +Y = Nat.is_le(b1, Norm.last_b(t, b))
  wh(fa, B.Fasta.find(fa, c), c, a, Norm.last_b(t, b), c1, a1, b1, {==},
    PB.and_true_l(String.eq(c, c1), Nat.is_le(a, a1), PB.and_true_l(X, Y, h)),
    PB.and_true_r(String.eq(c, c1), Nat.is_le(a, a1), PB.and_true_l(X, Y, h)),
    PB.and_true_r(X, Y, h))

# The not-held allowance can only drop when what is held grows.
law nimp:
  for +X: Bool
  for +Y: Bool
  for +n: Nat
  for h: @e: {Y == True{} : Bool} -> {X == True{} : Bool}
  {Nat.is_le(BN.pick(Bool.not(X), n), BN.pick(Bool.not(Y), n)) == True{} : Bool}

def nimp(X, Y, n, h):
  match Y:
    case True{}:
      %Equal.sym(Bool, X, True{}, h({==})) : {Nat.is_le(BN.pick(Bool.not(_), n), 0n) == True{} : Bool}
      {==}
    case False{}:
      BSt.pick_le1(Bool.not(X), n)

law or_imp:
  for +A: Bool
  for +X: Bool
  for +Y: Bool
  for +hy: {Bool.or(A, Y) == True{} : Bool}
  for h: @e: {Y == True{} : Bool} -> {X == True{} : Bool}
  {Bool.or(A, X) == True{} : Bool}

def or_imp(A, X, Y, hy, h):
  match A:
    case True{}:
      {==}
    case False{}:
      h(hy)

law rem_ref:
  for +fa: List<&2, B.Contig>
  for +fl: Bool
  for +back: Nat
  for +wp: PC.WP
  for +c: String
  for +a: Nat
  for +b: Nat
  for +t: List<&2, Pr.Req>
  for +l: B.Line
  {Nat.is_le(BN.rem(fa, fl, back, PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), None{}, l), BN.rem(fa, fl, back, PC.mkWin(fa, wp), Some{Pr.Req{c, a, b} <> t}, l)) == True{} : Bool}

def rem_ref(fa, fl, back, wp, c, a, b, t, l):
  +X = BN.holdsW(PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), BN.lchrom(l), BN.lp1(l), BN.lend(l))
  +Y = BN.coversA(Some{Pr.Req{c, a, b} <> t}, BN.lchrom(l), BN.lp1(l), BN.lend(l))
  +Z = Nat.add(BN.pick(Nat.is_eq(back, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(back, BN.lpos(l)), BN.ZW(fa)))
  +F = BN.pick(fl, BN.RW(l))
  BSt.pick_mono(BN.lgate(l), Nat.add(Nat.add(F, BN.pick(Bool.not(X), BN.RW(l))), Z), Nat.add(Nat.add(F, BN.pick(Bool.not(Y), BN.RW(l))), Z),
    N.le_add_mono_r(Z, Nat.add(F, BN.pick(Bool.not(X), BN.RW(l))), Nat.add(F, BN.pick(Bool.not(Y), BN.RW(l))),
      N.le_add_mono_l(F, BN.pick(Bool.not(X), BN.RW(l)), BN.pick(Bool.not(Y), BN.RW(l)),
        nimp(X, Y, BN.RW(l), e => cov_hold(fa, c, a, b, t, BN.lchrom(l), BN.lp1(l), BN.lend(l), e)))))

law wa_ref:
  for +fa: List<&2, B.Contig>
  for +fl: Bool
  for +back: Nat
  for +wp: PC.WP
  for +c: String
  for +a: Nat
  for +b: Nat
  for +t: List<&2, Pr.Req>
  for +ls: List<&2, B.Line>
  {Nat.is_le(BN.WA.ls(fa, fl, back, PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), None{}, ls), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), Some{Pr.Req{c, a, b} <> t}, ls)) == True{} : Bool}

def wa_ref(fa, fl, back, wp, c, a, b, t, ls):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +u}:
      BSt.add2(BN.rem(fa, fl, back, PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), None{}, l), BN.rem(fa, fl, back, PC.mkWin(fa, wp), Some{Pr.Req{c, a, b} <> t}, l),
        BN.LAs(fa, u), BN.LAs(fa, u), rem_ref(fa, fl, back, wp, c, a, b, t, l), N.le_refl(BN.LAs(fa, u)))

# bi's zero window (heldZ): the old window fits (contig c1, e <= its clen)
# and the Ask covers (c1, 0, e); the window set_win builds is for the same
# contig (so the same clen), from <= 0, to >= e: it holds (c1, 0, e) and fits.
def zfwk(+c0: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32, +c: String, +e: Nat) ->
  {BN.zfit(Norm.win_of.k(c0, a0, b0, clen, off, r), c, e) == Bool.and(String.eq(c0, c), Nat.is_le(e, clen)) : Bool}:
  match r:
    case (raw, rl):
      {==}

def zhwk(+c0: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32, +c: String, +e: Nat) ->
  {BN.zheld(Norm.win_of.k(c0, a0, b0, clen, off, r), c, e) == Bool.and(Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, 0n)), Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen))), Nat.is_le(e, clen)) : Bool}:
  match r:
    case (raw, rl):
      {==}

def and4(+x: Bool, +y: Bool, +z: Bool, +w: Bool, +hx: {x == True{} : Bool}, +hy: {y == True{} : Bool}, +hz: {z == True{} : Bool}, +hw: {w == True{} : Bool}) ->
  {Bool.and(Bool.and(Bool.and(x, y), z), w) == True{} : Bool}:
  %Equal.sym(Bool, w, True{}, hw) : {Bool.and(Bool.and(Bool.and(x, y), z), _) == True{} : Bool}
  %Equal.sym(Bool, Bool.and(Bool.and(x, y), z), True{}, and3(x, y, z, hx, hy, hz)) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# A fitting window: its contig is in the reference, with e within it.
def zfk(+fa: List<&2, B.Contig>, +m: Maybe<&2, String>, +c0: String, +a0: Nat, +b0: Nat, +str: Bool, +c1: String, +e: Nat,
  +hm: {B.Fasta.find(fa, c0) == m : Maybe<&2, String>},
  +h: {BN.zfit(PC.mkWin.k(m, c0, a0, b0, str), c1, e) == True{} : Bool}) ->
  &r: String -> ({B.Fasta.find(fa, c1) == Some{r} : Maybe<&2, String>} & {Nat.is_le(e, String.length(r)) == True{} : Bool}):
  match m str:
    case None{} _:
      Empty.absurd(&r: String -> ({B.Fasta.find(fa, c1) == Some{r} : Maybe<&2, String>} & {Nat.is_le(e, String.length(r)) == True{} : Bool}), PB.false_ne_true(h))
    case Some{+r} False{}:
      +X0 = Bool.and(String.eq(c0, c1), Nat.is_le(e, String.length(r)))
      +hx = Equal.trans(Bool, X0, BN.zfit(Norm.win_of.k(c0, a0, b0, String.length(r), Nat.min(a0, String.length(r)), BY.len(E.enc(PC.letters(r, a0, b0)))), c1, e), True{},
        Equal.sym(Bool, BN.zfit(Norm.win_of.k(c0, a0, b0, String.length(r), Nat.min(a0, String.length(r)), BY.len(E.enc(PC.letters(r, a0, b0)))), c1, e), X0,
          zfwk(c0, a0, b0, String.length(r), Nat.min(a0, String.length(r)), BY.len(E.enc(PC.letters(r, a0, b0))), c1, e)), h)
      (r, (AB.subst(String, z => {B.Fasta.find(fa, z) == Some{r} : Maybe<&2, String>}, c0, c1, RB.str_eq_sound(c0, c1, PB.and_true_l(String.eq(c0, c1), Nat.is_le(e, String.length(r)), hx)), hm),
        PB.and_true_r(String.eq(c0, c1), Nat.is_le(e, String.length(r)), hx)))
    case Some{+r} True{}:
      (r, (AB.subst(String, z => {B.Fasta.find(fa, z) == Some{r} : Maybe<&2, String>}, c0, c1, RB.str_eq_sound(c0, c1, PB.and_true_l(String.eq(c0, c1), Nat.is_le(e, String.length(r)), h)), hm),
        PB.and_true_r(String.eq(c0, c1), Nat.is_le(e, String.length(r)), h)))

def zf(+fa: List<&2, B.Contig>, +wp: PC.WP, +c1: String, +e: Nat,
  +h: {BN.zfit(PC.mkWin(fa, wp), c1, e) == True{} : Bool}) ->
  &r: String -> ({B.Fasta.find(fa, c1) == Some{r} : Maybe<&2, String>} & {Nat.is_le(e, String.length(r)) == True{} : Bool}):
  match wp:
    case PC.WPNone{}:
      Empty.absurd(&r: String -> ({B.Fasta.find(fa, c1) == Some{r} : Maybe<&2, String>} & {Nat.is_le(e, String.length(r)) == True{} : Bool}), PB.false_ne_true(h))
    case PC.WPUnk{+c0}:
      Empty.absurd(&r: String -> ({B.Fasta.find(fa, c1) == Some{r} : Maybe<&2, String>} & {Nat.is_le(e, String.length(r)) == True{} : Bool}), PB.false_ne_true(h))
    case PC.WPKnown{+c0, +a0, +b0}:
      zfk(fa, B.Fasta.find(fa, c0), c0, a0, b0, False{}, c1, e, {==}, h)
    case PC.WPStr{+c0, +a0, +b0}:
      zfk(fa, B.Fasta.find(fa, c0), c0, a0, b0, True{}, c1, e, {==}, h)

def zk(+r: String, +c: String, +a: Nat, +b: Nat, +str: Bool, +c1: String, +e: Nat,
  +hc: {String.eq(c, c1) == True{} : Bool}, +ha: {Nat.is_le(a, 0n) == True{} : Bool}, +hb: {Nat.is_le(e, b) == True{} : Bool},
  +hr: {Nat.is_le(e, String.length(r)) == True{} : Bool}) ->
  {BN.zheld(PC.mkWin.k(Some{r}, c, a, b, str), c1, e) == True{} : Bool}:
  match str:
    case False{}:
      +HZ = BN.zheld(Norm.win_of.k(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(PC.letters(r, a, b)))), c1, e)
      +X0 = Bool.and(Bool.and(Bool.and(String.eq(c, c1), Nat.is_le(a, 0n)), Nat.is_le(Nat.min(e, String.length(r)), Nat.min(b, String.length(r)))), Nat.is_le(e, String.length(r)))
      Equal.trans(Bool, HZ, X0, True{}, zhwk(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(PC.letters(r, a, b))), c1, e),
        and4(String.eq(c, c1), Nat.is_le(a, 0n), Nat.is_le(Nat.min(e, String.length(r)), Nat.min(b, String.length(r))), Nat.is_le(e, String.length(r)), hc, ha, min_mono(e, b, String.length(r), hb), hr))
    case True{}:
      and4(String.eq(c, c1), Nat.is_le(a, 0n), Nat.is_le(Nat.min(e, String.length(r)), Nat.min(b, String.length(r))), Nat.is_le(e, String.length(r)), hc, ha, min_mono(e, b, String.length(r), hb), hr)

def zh2(+fa: List<&2, B.Contig>, +g: Bool, +r: String, +c: String, +a: Nat, +b: Nat, +c1: String, +e: Nat,
  +hm: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {String.eq(c, c1) == True{} : Bool}, +ha: {Nat.is_le(a, 0n) == True{} : Bool}, +hb: {Nat.is_le(e, b) == True{} : Bool},
  +hr: {Nat.is_le(e, String.length(r)) == True{} : Bool}) ->
  {BN.zheld(PC.mkWin(fa, Bool.pick(PC.WP, g, PC.WPKnown{c, a, b}, PC.WPStr{c, a, b})), c1, e) == True{} : Bool}:
  match g:
    case True{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) : {BN.zheld(PC.mkWin.k(_, c, a, b, False{}), c1, e) == True{} : Bool}
      zk(r, c, a, b, False{}, c1, e, hc, ha, hb, hr)
    case False{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) : {BN.zheld(PC.mkWin.k(_, c, a, b, True{}), c1, e) == True{} : Bool}
      zk(r, c, a, b, True{}, c1, e, hc, ha, hb, hr)

def zcov.k(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +c1: String, +e: Nat,
  +hc: {String.eq(c, c1) == True{} : Bool}, +ha: {Nat.is_le(a, 0n) == True{} : Bool}, +hb: {Nat.is_le(e, b) == True{} : Bool},
  fr: &r: String -> ({B.Fasta.find(fa, c1) == Some{r} : Maybe<&2, String>} & {Nat.is_le(e, String.length(r)) == True{} : Bool})) ->
  {BN.zheld(PC.mkWin(fa, PC.wpOf(fa, c, a, b)), c1, e) == True{} : Bool}:
  (+r, f1) = fr
  (+hm1, hr) = f1
  +hm = AB.subst(String, z => {B.Fasta.find(fa, z) == Some{r} : Maybe<&2, String>}, c1, c, Equal.sym(String, c, c1, RB.str_eq_sound(c, c1, hc)), hm1)
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) : {BN.zheld(PC.mkWin(fa, PC.wpOf.k(_, c, a, b)), c1, e) == True{} : Bool}
  zh2(fa, Norm.le31(Nat.sub(b, a)), r, c, a, b, c1, e, hm, hc, ha, hb, hr)

def zcov(+fa: List<&2, B.Contig>, +wp: PC.WP, +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>, +c1: String, +e: Nat,
  +h: {Bool.and(BN.zfit(PC.mkWin(fa, wp), c1, e), BN.coversA(Some{Pr.Req{c, a, b} <> t}, c1, 0n, e)) == True{} : Bool}) ->
  {BN.zheld(PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), c1, e) == True{} : Bool}:
  +ZF = BN.zfit(PC.mkWin(fa, wp), c1, e)
  +CV = BN.coversA(Some{Pr.Req{c, a, b} <> t}, c1, 0n, e)
  +X = Bool.and(String.eq(c, c1), Nat.is_le(a, 0n))
  +Y = Nat.is_le(e, Norm.last_b(t, b))
  +hcv = PB.and_true_r(ZF, CV, h)
  zcov.k(fa, c, a, Norm.last_b(t, b), c1, e,
    PB.and_true_l(String.eq(c, c1), Nat.is_le(a, 0n), PB.and_true_l(X, Y, hcv)),
    PB.and_true_r(String.eq(c, c1), Nat.is_le(a, 0n), PB.and_true_l(X, Y, hcv)),
    PB.and_true_r(X, Y, hcv),
    zf(fa, wp, c1, e, PB.and_true_l(ZF, CV, h)))

law bi_ref:
  for +fa: List<&2, B.Contig>
  for +back: Nat
  for +wp: PC.WP
  for +c: String
  for +a: Nat
  for +b: Nat
  for +t: List<&2, Pr.Req>
  for +ls: List<&2, B.Line>
  for +h: {BN.bi.ls(back, PC.mkWin(fa, wp), Some{Pr.Req{c, a, b} <> t}, ls) == True{} : Bool}
  {BN.bi.ls(back, PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), None{}, ls) == True{} : Bool}

def bi_ref(fa, back, wp, c, a, b, t, ls, h):
  match ls:
    case Nil{}:
      h
    case Con{+l, +u}:
      or_imp(Nat.is_eq(back, 0n), BN.zheld(PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))), BN.lchrom(l), BN.lend(l)),
        Bool.and(BN.zfit(PC.mkWin(fa, wp), BN.lchrom(l), BN.lend(l)), BN.coversA(Some{Pr.Req{c, a, b} <> t}, BN.lchrom(l), 0n, BN.lend(l))), h,
        e => zcov(fa, wp, c, a, b, t, BN.lchrom(l), BN.lend(l), e))

# The Ask's answers: the window wpOf(c, a, bb) in place of the old one.
def ref_some(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed, dfs}), cs) == True{} : Bool},
  +hmw: {S.mb_win(md, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool},
  +wt2: {PC.wp_ok(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed, dfs}),
    S.mkSt(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, Norm.last_b(t, b)), None{}, fneed, dfs})):
  ?TODO


def ref_win2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed, dfs}), cs) == True{} : Bool},
  +hmw: {S.mb_win(md, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool},
  wt: {Norm.win_of(Norm.parts(c, a, Norm.last_b(t, b)), M.truths(fa, Norm.parts(c, a, Norm.last_b(t, b)))) == PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) : Norm.Win}
    & {PC.wp_ok(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed, dfs}),
    Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.win_of(Norm.parts(c, a, Norm.last_b(t, b)), M.truths(fa, Norm.parts(c, a, Norm.last_b(t, b)))), None{}, fneed, dfs}):
  (+wt1, wt2) = wt
  +bb = Norm.last_b(t, b)
  %Equal.sym(Norm.Win, Norm.win_of(Norm.parts(c, a, bb), M.truths(fa, Norm.parts(c, a, bb))), PC.mkWin(fa, PC.wpOf(fa, c, a, bb)), wt1) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed, dfs}), Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, _, None{}, fneed, dfs})
  ref_some(dfs, fa, T, cs, O, N, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, hb, hw, hr, hg, hbi, hmw, wt2)

# F3: the answers to the reads asked last.
def ref_fed(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +rs: List<&2, Pr.Req>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  +hq: {E.reqs_ok(rs) == True{} : Bool},
  +hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, p), Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs))):
  match rs p:
    case Nil{} S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, None{}, ha) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, _, fneed, dfs}), Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, _, fneed, dfs}), M.truths(fa, Nil{})))
      fed_leaf(dfs, fa, T, cs, cs, O, N, o, md, src, pd, eof, src, pd, eof, back, wp, fneed, hw,
        Equal.trans(R.Report, S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs}), S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), T,
          DS.rep_lines(dfs, fa, cs, cs, O, N, o, md, src, pd, eof, src, pd, eof, back, wp, asked, back, wp, None{}, fneed, fneed, {==}, {==}), hr),
        hg,
        AB.subst(Maybe<&2, List<&2, Pr.Req>>, z => {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, z, fneed, dfs}), cs) == True{} : Bool}, asked, None{}, ha, hbi),
        {==})
    case Con{Pr.Req{+c, +a, +b}, +t} S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +rs1 = {Con{Pr.Req{c, a, b}, t} : List<&2, Pr.Req>}
      +bb = Norm.last_b(t, b)
      +hbi1 = AB.subst(Maybe<&2, List<&2, Pr.Req>>, z => {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, z, fneed, dfs}), cs) == True{} : Bool}, asked, Some{rs1}, ha, hbi)
      %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, Some{rs1}, ha) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, _, fneed, dfs}), Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, _, fneed, dfs}), M.truths(fa, rs1)))
      %Equal.sym(List<&2, Pr.Req>, rs1, Norm.parts(c, a, bb), hp) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{rs1}, fneed, dfs}), Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.win_of(_, M.truths(fa, _)), None{}, fneed, dfs})
      ref_win2(dfs, fa, T, cs, O, N, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, hb, hw, hr, hg, hbi1, DS.mbw_of(md, fa, c, a, b, t, bb, hmr), PCA.win_truths(fa, c, a, bb, hb))
