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
import ./proof_b_enc.bend as EN
import ./proof_b_lines.bend as PL
import ./proof_b_lines_str.bend as LS
import ./proof_b_lines_pd.bend as LP
import ./proof_b_run.bend as RN
import ./proof_base.bend as PB
import ./proof_machine_nat.bend as PN
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_find.bend as FD
import ../lawful-bytes/proof_list.bend as Q
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-bytes/proof_grow.bend as G
import ./proof_b_lines_lst.bend as LT
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

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
  for +hl: {B.Text.lines(S.intext(S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed}, cs2)) == B.Text.lines(S.intext(S.StP{o, md, src, pd, eof, back, wp, None{}, fneed}, cs)) : List<&2, B.Line>}
  {BN.lines(P.mkSrcs(src2), P.mkPd(pd2), eof2, cs2) == BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs) : List<&2, B.Line>}

def lines_eq(cs2, cs, o, md, src2, pd2, eof2, src, pd, eof, back, wp, fneed, hl):
  +Q2 = {S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed} : S.StP}
  +Q0 = {S.StP{o, md, src, pd, eof, back, wp, None{}, fneed} : S.StP}
  +A2 = String.append(BN.srcT(P.mkSrcs(src2)), String.append(BN.pdT(P.mkPd(pd2)), S.concat_if(eof2, cs2)))
  +A0 = String.append(BN.srcT(P.mkSrcs(src)), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs)))
  Equal.trans(List<&2, B.Line>, B.Text.lines(A2), B.Text.lines(S.intext(Q2, cs2)), B.Text.lines(A0),
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), A2, S.intext(Q2, cs2), BL.text_pic(Q2, cs2)),
    Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(Q2, cs2)), B.Text.lines(S.intext(Q0, cs)), B.Text.lines(A0), hl,
      Equal.sym(List<&2, B.Line>, B.Text.lines(A0), B.Text.lines(S.intext(Q0, cs)),
        Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), A0, S.intext(Q0, cs), BL.text_pic(Q0, cs)))))

# A fed state that is the picture Q1 of Q0 with other sources, line end and
# eof, whose text has the same lines.
law fed_leaf:
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
  for +hw1: {S.WF(fa, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr1: {S.report(fa, cs2, O, N, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed}), cs) == True{} : Bool}
  for +hl: {B.Text.lines(S.intext(S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed}, cs2)) == B.Text.lines(S.intext(S.StP{o, md, src, pd, eof, back, wp, None{}, fneed}, cs)) : List<&2, B.Line>}
  BD.FedG(fa, T, cs2, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed}), S.mkSt(fa, S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed}))

def fed_leaf(fa, T, cs, cs2, O, N, o, md, src, pd, eof, src2, pd2, eof2, back, wp, fneed, hw1, hr1, hg, hbi, hl):
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd2), eof2, cs2)
  +L0 = BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +leq = lines_eq(cs2, cs, o, md, src2, pd2, eof2, src, pd, eof, back, wp, fneed, hl)
  +fl = BN.fast_left(S.mkMd(md), fneed)
  (S.StP{o, md, src2, pd2, eof2, back, wp, None{}, fneed}, ({==}, (hw1, (hr1, (hg, ({==},
    (le_eq(BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), None{}, L2), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), None{}, L0),
       Equal.cong(List<&2, B.Line>, Nat, z => BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), None{}, z), L2, L0, leq)),
     Equal.trans(Bool, BN.bi.ls(back, PC.mkWin(fa, wp), None{}, L2), BN.bi.ls(back, PC.mkWin(fa, wp), None{}, L0), True{},
       Equal.cong(List<&2, B.Line>, Bool, z => BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z), L2, L0, leq), hbi))))))))

# F1: the piece (proof_b_drive_chunk.bend's chain, ending in FedG)
# ==========================================================

# The line end is empty: the piece is the only source.
def ch_empty(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>},
  +he: {String.is_empty(P.pdtext(pd)) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.SB{CH.BTc(c), 0}]), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed}):
  +sp0 = {P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), 0} : P.SrcP}
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok([sp0]), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty([sp0]), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext([sp0])))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    LP.and_le0(D.ok(CH.BTc(c), CH.DD(c)), CH.L0(c), hok),
    DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), he, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, [sp0], pd, False{}, back, wp, None{}, fneed} : S.StP}
  +tx = CH.txt_e(P.srctext(sp0), c, P.pdtext(pd), String.concat(cs), CH.src0_text(c, hv), CH.emp_eq(P.pdtext(pd), he))
  +hl = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(p1, cs), S.intext(p0, c <> cs), tx)
  +hr1 = Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p0), T,
    DS.rep_lines(fa, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, [sp0], pd, False{}, back, wp, None{}, back, wp, None{}, fneed, fneed, hl), hr)
  fed_leaf(fa, T, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, [sp0], pd, False{}, back, wp, fneed, hw1, hr1, hg, hbi, hl)

# No LF in the piece: it goes to the line end.
def ch_all3(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +pp2: P.PdP,
  +e2: {Norm.pend.add(P.mkPd(pd), CH.BTc(c), 0, CH.L0(c)) == P.mkPd(pp2) : Norm.Pd},
  +hpo: {P.pd_ok(pp2) == True{} : Bool},
  +hpt: {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c))) : String},
  +hnc: {P.nolf(c) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), CH.BTc(c), 0, CH.L0(c)), False{}, back, PC.mkWin(fa, wp), None{}, fneed}):
  %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), CH.BTc(c), 0, CH.L0(c)), P.mkPd(pp2), e2) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), Nil{}, _, False{}, back, PC.mkWin(fa, wp), None{}, fneed})
  +hba = CH.bt_all(c, hok, hv)
  +hn3 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c))), P.pdtext(pp2), Equal.sym(String, P.pdtext(pp2), String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c))), hpt),
    LS.nolf_app(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c)), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
      AB.subst(String, z => {P.nolf(z) == True{} : Bool}, c, P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c)), Equal.sym(String, P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c)), c, hba), hnc)))
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pp2), P.nolf(P.pdtext(pp2)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pp2))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pp2)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), {==}, hpo, hn3, {==}, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, Nil{}, pp2, False{}, back, wp, None{}, fneed} : S.StP}
  +tx = CH.txt_a(P.pdtext(pp2), P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c)), c, String.concat(cs), hpt, hba)
  +hl = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(p1, cs), S.intext(p0, c <> cs), tx)
  +hr1 = Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p0), T,
    DS.rep_lines(fa, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, Nil{}, pp2, False{}, back, wp, None{}, back, wp, None{}, fneed, fneed, hl), hr)
  fed_leaf(fa, T, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, Nil{}, pp2, False{}, back, wp, fneed, hw1, hr1, hg, hbi, hl)

def ch_all2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>},
  +hnc: {P.nolf(c) == True{} : Bool},
  r: &pp2: P.PdP -> ({Norm.pend.add(P.mkPd(pd), C.BT(CH.L0(c), CH.ET(c)), 0, CH.L0(c)) == P.mkPd(pp2) : Norm.Pd}
    & ({P.pd_ok(pp2) == True{} : Bool}
    & {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(CH.L0(c), CH.ET(c), 0, CH.L0(c))) : String}))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), CH.BTc(c), 0, CH.L0(c)), False{}, back, PC.mkWin(fa, wp), None{}, fneed}):
  (+pp2, r1) = r
  (+e2, r2) = r1
  (hpo, hpt) = r2
  ch_all3(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, pp2, e2, hpo, hpt, hnc)

# The piece's LF at j joins the line end.
def ch_join3(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
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
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), CH.BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  %Equal.sym(Norm.Pd & D.Bytes, Norm.join.k(P.mkPd(pd), CH.BTc(c), j), (P.mkPd(pp2), CH.BTc(c)), ej) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.join(o, S.mkMd(md), j, _, False{}, back, PC.mkWin(fa, wp), None{}, fneed))
  %Equal.sym(Norm.Src, Norm.Pd.src(P.mkPd(pp2)), P.mkSrc(PL.pdsrc(pp2)), esrc) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), [_, Norm.SB{CH.BTc(c), (j + 1 : U32)}], Norm.PB{BY.empty(0n)}, False{}, back, PC.mkWin(fa, wp), None{}, fneed})
  %Equal.sym(Norm.Pd, Norm.PB{BY.empty(0n)}, P.mkPd(pp0), f1) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), [P.mkSrc(PL.pdsrc(pp2)), Norm.SB{CH.BTc(c), (j + 1 : U32)}], _, False{}, back, PC.mkWin(fa, wp), None{}, fneed})
  +sp1 = PL.pdsrc(pp2)
  +sp2 = {P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), (j + 1 : U32)} : P.SrcP}
  +A = P.pdtext(pd)
  +Bq = P.btext(CH.L0(c), CH.ET(c), 0, j)
  +hs1e = AB.subst(String, z => {S.ends_lf(z) == True{} : Bool}, String.append(String.append(A, Bq), "\n"), P.srctext(sp1),
    Equal.trans(String, String.append(String.append(A, Bq), "\n"), String.append(A, String.append(Bq, "\n")), P.srctext(sp1), LS.sassoc(A, Bq, "\n"),
      Equal.sym(String, P.srctext(sp1), String.append(A, String.append(Bq, "\n")),
        Equal.trans(String, P.srctext(sp1), String.append(A, P.btext(CH.L0(c), CH.ET(c), 0, (j + 1 : U32))), String.append(A, String.append(Bq, "\n")), hst,
          Equal.cong(String, String, z => String.append(A, z), P.btext(CH.L0(c), CH.ET(c), 0, (j + 1 : U32)), String.append(Bq, "\n"), hlf2)))),
    DS.ends_lf_lf(String.append(A, Bq)))
  +hsrcs = LP.and_tt(Bool.and(P.src_ok(sp1), S.ends_lf(P.srctext(sp1))), P.src_ok(sp2), LP.and_tt(P.src_ok(sp1), S.ends_lf(P.srctext(sp1)), hso, hs1e),
    LP.and_tt(D.ok(CH.BTc(c), CH.DD(c)), U32.is_le((j + 1 : U32), CH.L0(c)), hok, hj1))
  +hn0 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, "", P.pdtext(pp0), Equal.sym(String, P.pdtext(pp0), "", hpt0), {==})
  +he0 = AB.subst(String, z => {String.is_empty(z) == True{} : Bool}, "", P.pdtext(pp0), Equal.sym(String, P.pdtext(pp0), "", hpt0), {==})
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok([sp1, sp2]), P.pd_ok(pp0), P.nolf(P.pdtext(pp0)), Bool.or(S.src_empty([sp1, sp2]), String.is_empty(P.pdtext(pp0))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pp0)), S.ends_lf(P.srcstext([sp1, sp2])))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hsrcs, hpo0, hn0, he0, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, [sp1, sp2], pp0, False{}, back, wp, None{}, fneed} : S.StP}
  +tx = CH.txt_j(P.srctext(sp1), P.srctext(sp2), P.pdtext(pp0), A, P.btext(CH.L0(c), CH.ET(c), 0, (j + 1 : U32)), Bq, c, String.concat(cs), hst, hlf2, hpt0, hc2)
  +hl = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(p1, cs), S.intext(p0, c <> cs), tx)
  +hr1 = Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p0), T,
    DS.rep_lines(fa, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, [sp1, sp2], pp0, False{}, back, wp, None{}, back, wp, None{}, fneed, fneed, hl), hr)
  fed_leaf(fa, T, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, [sp1, sp2], pp0, False{}, back, wp, fneed, hw1, hr1, hg, hbi, hl)

def ch_join2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
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
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), CH.BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  (+pp2, r1) = r
  (+ej, r2) = r1
  (+esrc, r3) = r2
  (hso, hst) = r3
  (+pp0, pe1) = pe
  (+f1, pe2) = pe1
  (hpo0, hpt0) = pe2
  ch_join3(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, pp2, pp0, ej, esrc, hso, hst, f1, hpo0, hpt0, hlf2, hc2, hj1)

def ch_join(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +hk: {Nat.is_lt(U32.to_nat(j), U32.to_nat(CH.L0(c))) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(CH.BTc(c)), U32.to_nat(j)) == Some{10} : Maybe<&2, U32>},
  sl: {P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), 0}) == String.append(P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32)), String.append("\n", P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), (j + 1 : U32)}))) : String}
  & ({P.nolf(P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32))) == True{} : Bool}
  & ({U32.is_le((j + 1 : U32), CH.L0(c)) == True{} : Bool}
  & {E.is_bytes(P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32))) == True{} : Bool}))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), CH.BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  (+h1, s1) = sl
  (+h2, s2) = s1
  (+h3, h4) = s2
  +hn2 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32)), P.btext(CH.L0(c), CH.ET(c), 0, j), CH.bt0(CH.L0(c), CH.ET(c), j), h2)
  +hc2 = Equal.trans(String, c, P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), 0}), String.append(P.btext(CH.L0(c), CH.ET(c), 0, j), String.append("\n", P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), (j + 1 : U32)}))),
    Equal.sym(String, P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), 0}), c, CH.src0_text(c, hv)),
    AB.subst(String, z => {P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), 0}) == String.append(z, String.append("\n", P.srctext(P.SBP{CH.L0(c), CH.ET(c), CH.DD(c), (j + 1 : U32)}))) : String},
      P.btext(CH.L0(c), CH.ET(c), 0, (j - 0 : U32)), P.btext(CH.L0(c), CH.ET(c), 0, j), CH.bt0(CH.L0(c), CH.ET(c), j), h1))
  ch_join2(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, LP.bt_lf(CH.L0(c), CH.ET(c), CH.DD(c), j, hok, hk, hlf), hc2, h3,
    PL.join_ok(pd, CH.L0(c), CH.ET(c), CH.DD(c), j, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hok, hk, hlf, DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hn2),
    PL.pd_empty())

# After the piece's first LF search.
def ch_z(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32, +z: Bool,
  +ez: {U32.is_eq(j, CH.L0(c)) == z : Bool},
  +hf: {U32.to_nat(j) == D.first(D.view(CH.BTc(c)), U32.to_nat(0), U32.to_nat(CH.L0(c)), 10) : Nat}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.lf(z, o, S.mkMd(md), CH.BTc(c), j, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  match z:
    case True{}:
      +V = D.view(CH.BTc(c))
      +nL = U32.to_nat(CH.L0(c))
      +hlen = Equal.sym(Nat, List.length(&2, U32, V), nL, O.view_size_t(CH.L0(c), CH.ET(c), CH.DD(c), hok))
      +ht = AB.subst(Nat, w => {Nat.is_le(nL, w) == True{} : Bool}, nL, List.length(&2, U32, V), hlen, N.le_refl(nL))
      +ejL = U.is_eq_true(j, CH.L0(c), ez)
      +hfL = AB.subst(U32, w => {U32.to_nat(w) == D.first(V, U32.to_nat(0), nL, 10) : Nat}, j, CH.L0(c), ejL, hf)
      sn = PL.src_nolf(CH.L0(c), CH.ET(c), CH.DD(c), 0, hok, LP.u32_le0(CH.L0(c)), Equal.sym(Nat, nL, D.first(V, U32.to_nat(0), nL, 10), hfL))
      ch_all2(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, CH.ch_nolf(c, sn, hv), PL.pend_add(pd, CH.L0(c), CH.ET(c), CH.DD(c), 0, CH.L0(c), DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hok, N.le_refl(nL)))
    case False{}:
      +V = D.view(CH.BTc(c))
      +nL = U32.to_nat(CH.L0(c))
      +hlen = Equal.sym(Nat, List.length(&2, U32, V), nL, O.view_size_t(CH.L0(c), CH.ET(c), CH.DD(c), hok))
      +ht = AB.subst(Nat, w => {Nat.is_le(nL, w) == True{} : Bool}, nL, List.length(&2, U32, V), hlen, N.le_refl(nL))
      +hr0 = Q.first_range(V, U32.to_nat(0), nL, 10, N.le_zero_l(nL), ht)
      +hjl = AB.subst(Nat, w => {Nat.is_le(w, nL) == True{} : Bool}, D.first(V, U32.to_nat(0), nL, 10), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf),
        AB.and_true_r(Nat.is_le(U32.to_nat(0), D.first(V, U32.to_nat(0), nL, 10)), Nat.is_le(D.first(V, U32.to_nat(0), nL, 10), nL), hr0))
      +hne = Equal.trans(Bool, Nat.is_eq(U32.to_nat(j), nL), U32.is_eq(j, CH.L0(c)), False{}, Equal.sym(Bool, U32.is_eq(j, CH.L0(c)), Nat.is_eq(U32.to_nat(j), nL), U.is_eq_to_nat(j, CH.L0(c))), ez)
      +hk = Equal.trans(Bool, Nat.is_lt(U32.to_nat(j), nL), Nat.is_le(1n+U32.to_nat(j), nL), True{}, Equal.sym(Bool, Nat.is_le(1n+U32.to_nat(j), nL), Nat.is_lt(U32.to_nat(j), nL), N.le_succ_lt(U32.to_nat(j), nL)),
        N.le_ne(U32.to_nat(j), nL, hjl, hne))
      +hfl = AB.subst(Nat, w => {Nat.is_lt(w, nL) == True{} : Bool}, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf, hk)
      +hhit = AB.subst(Nat, w => {D.has(V, w, 10) == True{} : Bool}, D.first(V, U32.to_nat(0), nL, 10), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf),
        Q.first_hit(V, U32.to_nat(0), nL, 10, N.le_zero_l(nL), ht, hfl))
      +hlf = LT.has_get(List.get(&2, U32, V, U32.to_nat(j)), 10, hhit)
      ch_join(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, hk, hlf, PL.src_line(CH.L0(c), CH.ET(c), CH.DD(c), 0, j, hok, LP.u32_le0(CH.L0(c)), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf), hk))

def ch_lf2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +e1: {NF.lf(CH.BTc(c), 0) == NF.Tb{CH.BTc(c), j, U32.is_eq(j, CH.L0(c)), False{}} : NF.Tb},
  +hf: {U32.to_nat(j) == D.first(D.view(CH.BTc(c)), U32.to_nat(0), U32.to_nat(CH.L0(c)), 10) : Nat}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.find(o, S.mkMd(md), NF.lf(CH.BTc(c), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  %Equal.sym(NF.Tb, NF.lf(CH.BTc(c), 0), NF.Tb{CH.BTc(c), j, U32.is_eq(j, CH.L0(c)), False{}}, e1) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.find(o, S.mkMd(md), _, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed))
  ch_z(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, U32.is_eq(j, CH.L0(c)), {==}, hf)

def ch_lf(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>},
  r: &j: U32 -> ({NF.lf(C.BT(CH.L0(c), CH.ET(c)), 0) == NF.Tb{C.BT(CH.L0(c), CH.ET(c)), j, U32.is_eq(j, CH.L0(c)), False{}} : NF.Tb}
    & {PL.n(j) == D.first(PL.xs(CH.L0(c), CH.ET(c)), PL.n(0), PL.n(CH.L0(c)), 10) : Nat})) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.find(o, S.mkMd(md), NF.lf(CH.BTc(c), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  (+j, r1) = r
  (e1, hf) = r1
  ch_lf2(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, j, e1, hf)

def core_if(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}, +z: Bool,
  +ez: {Nat.is_eq(String.length(P.pdtext(pd)), 0n) == z : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.if(z, o, S.mkMd(md), Nil{}, CH.BTc(c), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  match z:
    case True{}:
      ch_empty(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, DS.empty_of_len(P.pdtext(pd), ez))
    case False{}:
      ch_lf(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, PL.lf_ok(CH.L0(c), CH.ET(c), CH.DD(c), 0, hok, LP.u32_le0(CH.L0(c))))

def core(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(CH.BTc(c), CH.DD(c)) == True{} : Bool},
  +hv: {D.view(CH.BTc(c)) == E.codes(c) : List<&2, U32>}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  %Equal.sym(Norm.Pd & Nat, Norm.Pd.len(P.mkPd(pd)), (P.mkPd(pd), String.length(P.pdtext(pd))), PL.pd_len(pd, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), _, False{}, back, PC.mkWin(fa, wp), None{}, fneed))
  core_if(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, Nat.is_eq(String.length(P.pdtext(pd)), 0n), {==})

# The run gets room for the piece
# ===============================

def chunk_mb2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(CH.L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(CH.L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>},
  +e: {NR.reserve(P.mkRun(rp), CH.L0(c)) == P.mkRun(rp2) : NR.Run},
  +hi2: {RN.RunInv(rp2) == True{} : Bool},
  +hs: {P.specRun(rp2) == P.specRun(rp) : R.RunSt}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), CH.L0(c))}, Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  +md = {S.MBP{rp} : S.MdP}
  +md2 = {S.MBP{rp2} : S.MdP}
  +hw2 = DO.x9_mk(S.md_ok(md2), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md2, wp), E.all_bytes(S.opts_args(o)), hi2,
    DO.x9_1(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_4(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_5(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +q2 = {S.StP{o, md2, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +hr2 = Equal.trans(R.Report, S.report(fa, c <> cs, O, N, q2), S.report(fa, c <> cs, O, N, q), T,
    Equal.cong(R.RunSt, R.Report, z => R.finish(L.run.go(B.Text.lines(S.intext(q, c <> cs)), fa, o, S.pre(O, N, z))), P.specRun(rp2), P.specRun(rp), hs), hr)
  +hg2 = AB.subst(R.RunSt, z => {Bool.or(R.RunSt.inbody(z), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}, P.specRun(rp), P.specRun(rp2),
    Equal.sym(R.RunSt, P.specRun(rp2), P.specRun(rp), hs), hg)
  %Equal.sym(NR.Run, NR.reserve(P.mkRun(rp), CH.L0(c)), P.mkRun(rp2), e) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed))
  core(fa, T, c, cs, O, N, o, md2, pd, back, wp, fneed, hb, hw2, hr2, hg2, hbi, hok, hv)

def chunk_mb(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(CH.L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(CH.L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>},
  r: &p2: P.RunP -> ({NR.reserve(P.mkRun(rp), CH.L0(c)) == P.mkRun(p2) : NR.Run}
    & ({RN.RunInv(p2) == True{} : Bool}
    & ({P.specRun(p2) == P.specRun(rp) : R.RunSt}
    & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32})))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), CH.L0(c))}, Nil{}, C.BT(CH.L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  (+rp2, r1) = r
  (+e, r2) = r1
  (+hi2, r3) = r2
  (hs, ho) = r3
  chunk_mb2(fa, T, c, cs, O, N, o, rp, rp2, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv, e, hi2, hs)

# By the run's mode (the String mode's run has no buffer).
def chunk_md(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(CH.L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(CH.L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), C.BT(CH.L0(c), EN.enc_t(c)))):
  match md:
    case S.MBP{+rp}:
      chunk_mb(fa, T, c, cs, O, N, o, rp, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv,
        RN.run_reserve(rp, CH.L0(c), DO.x8_a(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), E.all_bytes(S.opts_args(o)), hw)))
    case S.MSP{+s, +qs, +ql, +code}:
      core(fa, T, c, cs, O, N, o, S.MSP{s, qs, ql, code}, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv)

# The piece's facts from the enc area.
def chunk_enc(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), c <> cs) == True{} : Bool},
  r: {D.ok(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), C.BT(CH.L0(c), EN.enc_t(c)))):
  (hok, r1) = r
  (hv, r2) = r1
  chunk_md(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hok, hv)

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
    case S.StP{+o, +md, Con{+x, +t}, +pd, +eof, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Con{x, t}, pd, eof, back, wp, asked, fneed} : S.StP}
      Empty.absurd(BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), E.enc(c))),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed} : S.StP}
      Empty.absurd(BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), E.enc(c))),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed} : S.StP}
      Empty.absurd(BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), E.enc(c))),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
      +hw = DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm)
      %Equal.sym(D.Bytes, E.enc(c), C.BT(CH.L0(c), EN.enc_t(c)), EN.enc_bt(c)) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), _))
      chunk_enc(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, EN.enc_ok(c, hcb, hcn))

# F2: the end of the file (proof_b_drive_step.bend's eof chain, ending in FedG)
# ======================================================================

law eof_empty:
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
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Nil{}) == True{} : Bool}
  for +he: {String.is_empty(P.pdtext(pd)) == True{} : Bool}
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), S.mkSt(fa, S.StP{o, md, Nil{}, pd, True{}, back, wp, None{}, fneed}))

def eof_empty(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, he):
  +hw1 = DO.x9_mk(S.md_ok(md), True{}, P.pd_ok(pd), P.nolf(P.pdtext(pd)), True{}, Bool.and(String.is_empty(P.pdtext(pd)), True{}), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)),
    DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), {==}, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), {==},
    %Equal.sym(Bool, String.is_empty(P.pdtext(pd)), True{}, he) : {Bool.and(_, True{}) == True{} : Bool}; {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p1 = {S.StP{o, md, Nil{}, pd, True{}, back, wp, None{}, fneed} : S.StP}
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  fed_leaf(fa, T, Nil{}, Nil{}, O, N, o, md, Nil{}, pd, False{}, Nil{}, pd, True{}, back, wp, fneed, hw1,
    Equal.trans(R.Report, S.report(fa, Nil{}, O, N, p1), S.report(fa, Nil{}, O, N, p0), T,
      DS.rep_lines(fa, Nil{}, Nil{}, O, N, o, md, Nil{}, pd, False{}, Nil{}, pd, True{}, back, wp, None{}, back, wp, None{}, fneed, fneed, {==}), hr),
    hg, hbi, {==})

law eof_full2:
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
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Nil{}) == True{} : Bool}
  for +hne: {String.is_empty(P.pdtext(pd)) == False{} : Bool}
  for +e1: {Norm.eof_src(P.mkPd(pd)) == P.mkSrc(sp) : Norm.Src}
  for +hso: {P.src_ok(sp) == True{} : Bool}
  for +hst: {P.srctext(sp) == String.append(P.pdtext(pd), "\n") : String}
  for +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp0) : Norm.Pd}
  for +hpo: {P.pd_ok(pp0) == True{} : Bool}
  for +hpt: {P.pdtext(pp0) == "" : String}
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.eof_src(P.mkPd(pd))]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed})

def eof_full2(fa, T, O, N, o, md, pd, back, wp, fneed, sp, pp0, hb, hw, hr, hg, hbi, hne, e1, hso, hst, f1, hpo, hpt):
  %Equal.sym(Norm.Src, Norm.eof_src(P.mkPd(pd)), P.mkSrc(sp), e1) :
    BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [_]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed})
  %Equal.sym(Norm.Pd, Norm.PB{BY.empty(0n)}, P.mkPd(pp0), f1) :
    BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), [P.mkSrc(sp)], _, True{}, back, PC.mkWin(fa, wp), None{}, fneed})
  +X = P.pdtext(pd)
  +hw2 = DO.x9_mk(S.md_ok(md), P.src_ok(sp), P.pd_ok(pp0), P.nolf(P.pdtext(pp0)), String.is_empty(P.pdtext(pp0)),
    Bool.and(String.is_empty(P.pdtext(pp0)), S.ends_lf(String.append(P.srctext(sp), ""))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)),
    DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hso, hpo,
    %Equal.sym(String, P.pdtext(pp0), "", hpt) : {P.nolf(_) == True{} : Bool}; {==},
    %Equal.sym(String, P.pdtext(pp0), "", hpt) : {String.is_empty(_) == True{} : Bool}; {==},
    DS.b5_eof(X, P.srctext(sp), P.pdtext(pp0), hst, hpt),
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p2 = {S.StP{o, md, [sp], pp0, True{}, back, wp, None{}, fneed} : S.StP}
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +hl = DS.lines_eof2(X, P.srctext(sp), P.pdtext(pp0), hst, hpt, DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hne)
  fed_leaf(fa, T, Nil{}, Nil{}, O, N, o, md, Nil{}, pd, False{}, [sp], pp0, True{}, back, wp, fneed, hw2,
    Equal.trans(R.Report, S.report(fa, Nil{}, O, N, p2), S.report(fa, Nil{}, O, N, p0), T,
      DS.rep_lines(fa, Nil{}, Nil{}, O, N, o, md, Nil{}, pd, False{}, [sp], pp0, True{}, back, wp, None{}, back, wp, None{}, fneed, fneed, hl), hr),
    hg, hbi, hl)

law eof_full:
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
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Nil{}) == True{} : Bool}
  for +hne: {String.is_empty(P.pdtext(pd)) == False{} : Bool}
  for eo: &sp: P.SrcP -> ({Norm.eof_src(P.mkPd(pd)) == P.mkSrc(sp) : Norm.Src} & ({P.src_ok(sp) == True{} : Bool} & {P.srctext(sp) == String.append(P.pdtext(pd), "\n") : String}))
  for pe: &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd} & ({P.pd_ok(pp) == True{} : Bool} & {P.pdtext(pp) == "" : String}))
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.eof_src(P.mkPd(pd))]), Norm.PB{BY.empty(0n)}, True{}, back, PC.mkWin(fa, wp), None{}, fneed})

def eof_full(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hne, eo, pe):
  (+sp, eo1) = eo
  (+e1, eo2) = eo1
  (hso, hst) = eo2
  (+pp0, pe1) = pe
  (+f1, pe2) = pe1
  (hpo, hpt) = pe2
  eof_full2(fa, T, O, N, o, md, pd, back, wp, fneed, sp, pp0, hb, hw, hr, hg, hbi, hne, e1, hso, hst, f1, hpo, hpt)

law eof_if:
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
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Nil{}) == True{} : Bool}
  for +hc: {Nat.is_eq(String.length(P.pdtext(pd)), 0n) == c : Bool}
  BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed_eof.if(c, o, S.mkMd(md), Nil{}, P.mkPd(pd), back, PC.mkWin(fa, wp), None{}, fneed))

def eof_if(c, fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, hc):
  match c:
    case True{}:
      eof_empty(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, DS.empty_of_len(P.pdtext(pd), hc))
    case False{}:
      +hp = DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)
      eof_full(fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, DS.nonempty_of_len(P.pdtext(pd), hc), PL.eof_ok(pd, hp, DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)), PL.pd_empty())

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
  match p:
    case S.StP{+o, +md, Con{+x, +t}, +pd, +eof, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Con{x, t}, pd, eof, back, wp, asked, fneed} : S.StP}
      Empty.absurd(BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, q), Norm.feed_eof(S.mkSt(fa, q))),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed} : S.StP}
      Empty.absurd(BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, q), Norm.feed_eof(S.mkSt(fa, q))),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed} : S.StP}
      Empty.absurd(BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, q), Norm.feed_eof(S.mkSt(fa, q))),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
      +hw = DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm)
      +hp = DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)
      %Equal.sym(Norm.Pd & Nat, Norm.Pd.len(P.mkPd(pd)), (P.mkPd(pd), String.length(P.pdtext(pd))), PL.pd_len(pd, hp)) :
        BD.FedG(fa, T, Nil{}, O, N, BD.WP(fa, Nil{}, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Norm.feed_eof.k(o, S.mkMd(md), Nil{}, _, back, PC.mkWin(fa, wp), None{}, fneed))
      eof_if(Nat.is_eq(String.length(P.pdtext(pd)), 0n), fa, T, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hbi, {==})


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
def ref_some(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed}), cs) == True{} : Bool},
  +hmw: {S.mb_win(md, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool},
  +wt2: {PC.wp_ok(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed}),
    S.mkSt(fa, S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, Norm.last_b(t, b)), None{}, fneed})):
  +bb = Norm.last_b(t, b)
  +hw2 = DO.x9_mk(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
    Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, PC.wpOf(fa, c, a, bb)), S.mb_win(md, PC.wpOf(fa, c, a, bb)), E.all_bytes(S.opts_args(o)),
    DO.x8_a(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_1(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_2(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_3(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_4(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    DO.x9_5(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), wt2, hmw, DO.x9_8(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p1 = {S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, bb), None{}, fneed} : S.StP}
  +L0 = BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +fl = BN.fast_left(S.mkMd(md), fneed)
  (p1, ({==}, (hw2, (Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), T,
      DS.rep_lines(fa, cs, cs, O, N, o, md, src, pd, eof, src, pd, eof, back, wp, asked, back, PC.wpOf(fa, c, a, bb), None{}, fneed, fneed, {==}), hr),
    (hg, ({==}, (wa_ref(fa, fl, back, wp, c, a, b, t, L0), bi_ref(fa, back, wp, c, a, b, t, L0, hbi))))))))

def ref_win2(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +c: String, +a: Nat, +b: Nat, +t: List<&2, Pr.Req>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed}), cs) == True{} : Bool},
  +hmw: {S.mb_win(md, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool},
  wt: {Norm.win_of(Norm.parts(c, a, Norm.last_b(t, b)), M.truths(fa, Norm.parts(c, a, Norm.last_b(t, b)))) == PC.mkWin(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) : Norm.Win}
    & {PC.wp_ok(fa, PC.wpOf(fa, c, a, Norm.last_b(t, b))) == True{} : Bool}) ->
  BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed}),
    Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.win_of(Norm.parts(c, a, Norm.last_b(t, b)), M.truths(fa, Norm.parts(c, a, Norm.last_b(t, b)))), None{}, fneed}):
  (+wt1, wt2) = wt
  +bb = Norm.last_b(t, b)
  %Equal.sym(Norm.Win, Norm.win_of(Norm.parts(c, a, bb), M.truths(fa, Norm.parts(c, a, bb))), PC.mkWin(fa, PC.wpOf(fa, c, a, bb)), wt1) :
    BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{Pr.Req{c, a, b} <> t}, fneed}), Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, _, None{}, fneed})
  ref_some(fa, T, cs, O, N, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, hb, hw, hr, hg, hbi, hmw, wt2)

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
    case Nil{} S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, None{}, ha) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, _, fneed}), Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, _, fneed}), M.truths(fa, Nil{})))
      fed_leaf(fa, T, cs, cs, O, N, o, md, src, pd, eof, src, pd, eof, back, wp, fneed, hw,
        Equal.trans(R.Report, S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, None{}, fneed}), S.report(fa, cs, O, N, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), T,
          DS.rep_lines(fa, cs, cs, O, N, o, md, src, pd, eof, src, pd, eof, back, wp, asked, back, wp, None{}, fneed, fneed, {==}), hr),
        hg,
        AB.subst(Maybe<&2, List<&2, Pr.Req>>, z => {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, z, fneed}), cs) == True{} : Bool}, asked, None{}, ha, hbi),
        {==})
    case Con{Pr.Req{+c, +a, +b}, +t} S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      +rs1 = {Con{Pr.Req{c, a, b}, t} : List<&2, Pr.Req>}
      +bb = Norm.last_b(t, b)
      +hbi1 = AB.subst(Maybe<&2, List<&2, Pr.Req>>, z => {BN.biS(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, z, fneed}), cs) == True{} : Bool}, asked, Some{rs1}, ha, hbi)
      %Equal.sym(Maybe<&2, List<&2, Pr.Req>>, asked, Some{rs1}, ha) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, _, fneed}), Norm.set_win(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, _, fneed}), M.truths(fa, rs1)))
      %Equal.sym(List<&2, Pr.Req>, rs1, Norm.parts(c, a, bb), hp) :
        BD.FedG(fa, T, cs, O, N, BD.WP(fa, cs, S.StP{o, md, src, pd, eof, back, wp, Some{rs1}, fneed}), Norm.St{o, S.mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, Norm.win_of(_, M.truths(fa, _)), None{}, fneed})
      ref_win2(fa, T, cs, O, N, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, hb, hw, hr, hg, hbi1, DS.mbw_of(md, fa, c, a, b, t, bb, hmr), PCA.win_truths(fa, c, a, bb, hb))
