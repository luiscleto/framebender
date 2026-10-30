import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
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

# step_chunk (proof_b_drive.bend): a piece c given to a state waiting for
# more input. Norm.step feeds it (norm.bend's feed: room in the output
# buffer, then by the line end's length and the piece's first LF: the piece
# as the only source, or added to the line end, or the joined line and the
# rest of the piece as two sources), then go. The fed state is good, stands
# for the same report and keeps the guard, so DS.go_ok ends the step.
# The nine-test argument lists of S.WF (DO.x9_mk, DO.x9_k) were written by a
# small generator; edit them directly.

# The piece as a mirror
# =====================

def L0(+c: String) -> U32:
  U32.from_nat(String.length(c))

# The text of the piece's buffer is the piece.
def piece_text(+c: String, +hv: {D.view(C.BT(L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}) ->
  {NR.chars(D.view(C.BT(L0(c), EN.enc_t(c)))) == c : String}:
  %Equal.sym(List<&2, U32>, D.view(C.BT(L0(c), EN.enc_t(c))), E.codes(c), hv) : {NR.chars(_) == c : String}
  LS.chars_codes(c)

# Facts about texts
# =================

def ET(+c: String) -> AT.Tree<U32>:
  EN.enc_t(c)

def DD(+c: String) -> Nat:
  E.depth(String.length(c))

def BTc(+c: String) -> D.Bytes:
  C.BT(L0(c), EN.enc_t(c))

def emp_eq(+s: String, +h: {String.is_empty(s) == True{} : Bool}) -> {s == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+a, +t}:
      Empty.absurd({SCon{a, t} == "" : String}, PB.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))

# The piece read from 0 is the piece.
def src0_text(+c: String, +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}) ->
  {P.srctext(P.SBP{L0(c), ET(c), DD(c), 0}) == c : String}:
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, D.view(BTc(c)), 0n), D.view(BTc(c)), FD.drop_zero(D.view(BTc(c)))) : {NR.chars(_) == c : String}
  piece_text(c, hv)

# All of the piece's bytes are the piece.
def bt_all(+c: String, +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool}, +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}) ->
  {P.btext(L0(c), ET(c), 0, L0(c)) == c : String}:
  +V = D.view(BTc(c))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, FD.drop_zero(V)) : {NR.chars(List.take(&2, U32, _, U32.to_nat(L0(c)))) == c : String}
  %O.view_size_t(L0(c), ET(c), DD(c), hok) : {NR.chars(List.take(&2, U32, V, _)) == c : String}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, V, List.length(&2, U32, V)), V, G.take_all(V)) : {NR.chars(_) == c : String}
  piece_text(c, hv)

# Bytes 0 .. j - 0 are bytes 0 .. j.
def bt0(+len: U32, +t: AT.Tree<U32>, +j: U32) -> {P.btext(len, t, 0, (j - 0 : U32)) == P.btext(len, t, 0, j) : String}:
  Equal.cong(Nat, String, v => NR.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(0), v)), U32.to_nat((j - 0 : U32)), U32.to_nat(j),
    Equal.trans(Nat, U32.to_nat((j - 0 : U32)), Nat.sub(U32.to_nat(j), U32.to_nat(0)), U32.to_nat(j), U.to_nat_sub_le(j, 0, LP.u32_le0(j)), N.sub_zero(U32.to_nat(j))))

# The text still to come, in each case.
def txt_e(+X: String, +c: String, +P0: String, +Cc: String, +h1: {X == c : String}, +h2: {P0 == "" : String}) ->
  {String.append(String.append(X, ""), String.append(P0, Cc)) == String.append(P0, String.append(c, Cc)) : String}:
  %Equal.sym(String, P0, "", h2) : {String.append(String.append(X, ""), String.append(_, Cc)) == String.append(_, String.append(c, Cc)) : String}
  %Equal.sym(String, X, c, h1) : {String.append(String.append(_, ""), Cc) == String.append(c, Cc) : String}
  %Equal.sym(String, String.append(c, ""), c, PN.str_nil(c)) : {String.append(_, Cc) == String.append(c, Cc) : String}
  {==}

def txt_a(+Qt: String, +A: String, +Bt: String, +c: String, +Cc: String, +h1: {Qt == String.append(A, Bt) : String}, +h2: {Bt == c : String}) ->
  {String.append(Qt, Cc) == String.append(A, String.append(c, Cc)) : String}:
  %Equal.sym(String, Qt, String.append(A, Bt), h1) : {String.append(_, Cc) == String.append(A, String.append(c, Cc)) : String}
  %Equal.sym(String, Bt, c, h2) : {String.append(String.append(A, _), Cc) == String.append(A, String.append(c, Cc)) : String}
  LS.sassoc(A, c, Cc)

def txt_j(+S1: String, +S2: String, +P0: String, +A: String, +Bt1: String, +Bq: String, +c: String, +Cc: String,
  +h1: {S1 == String.append(A, Bt1) : String}, +h2: {Bt1 == String.append(Bq, "\n") : String}, +h3: {P0 == "" : String},
  +h4: {c == String.append(Bq, String.append("\n", S2)) : String}) ->
  {String.append(String.append(S1, String.append(S2, "")), String.append(P0, Cc)) == String.append(A, String.append(c, Cc)) : String}:
  %Equal.sym(String, P0, "", h3) : {String.append(String.append(S1, String.append(S2, "")), String.append(_, Cc)) == String.append(A, String.append(c, Cc)) : String}
  %Equal.sym(String, S1, String.append(A, Bt1), h1) : {String.append(String.append(_, String.append(S2, "")), Cc) == String.append(A, String.append(c, Cc)) : String}
  %Equal.sym(String, Bt1, String.append(Bq, "\n"), h2) : {String.append(String.append(String.append(A, _), String.append(S2, "")), Cc) == String.append(A, String.append(c, Cc)) : String}
  %Equal.sym(String, c, String.append(Bq, String.append("\n", S2)), h4) : {String.append(String.append(String.append(A, String.append(Bq, "\n")), String.append(S2, "")), Cc) == String.append(A, String.append(_, Cc)) : String}
  %Equal.sym(String, String.append(S2, ""), S2, PN.str_nil(S2)) : {String.append(String.append(String.append(A, String.append(Bq, "\n")), _), Cc) == String.append(A, String.append(String.append(Bq, String.append("\n", S2)), Cc)) : String}
  %Equal.sym(String, String.append(String.append(String.append(A, String.append(Bq, "\n")), S2), Cc), String.append(String.append(A, String.append(Bq, "\n")), String.append(S2, Cc)), LS.sassoc(String.append(A, String.append(Bq, "\n")), S2, Cc)) : {_ == String.append(A, String.append(String.append(Bq, String.append("\n", S2)), Cc)) : String}
  %Equal.sym(String, String.append(String.append(A, String.append(Bq, "\n")), String.append(S2, Cc)), String.append(A, String.append(String.append(Bq, "\n"), String.append(S2, Cc))), LS.sassoc(A, String.append(Bq, "\n"), String.append(S2, Cc))) : {_ == String.append(A, String.append(String.append(Bq, String.append("\n", S2)), Cc)) : String}
  %Equal.sym(String, String.append(String.append(Bq, "\n"), String.append(S2, Cc)), String.append(Bq, String.append("\n", String.append(S2, Cc))), LS.sassoc(Bq, "\n", String.append(S2, Cc))) : {String.append(A, _) == String.append(A, String.append(String.append(Bq, String.append("\n", S2)), Cc)) : String}
  %Equal.sym(String, String.append(String.append(Bq, String.append("\n", S2)), Cc), String.append(Bq, String.append(String.append("\n", S2), Cc)), LS.sassoc(Bq, String.append("\n", S2), Cc)) : {String.append(A, String.append(Bq, String.append("\n", String.append(S2, Cc)))) == String.append(A, _) : String}
  {==}

# The core: after the room, by the line end's length
# ==================================================

# The piece has no LF when its first LF is its end.
def ch_nolf(+c: String,
  sn: {P.nolf(P.srctext(P.SBP{L0(c), ET(c), DD(c), 0})) == True{} : Bool}
  & {P.srctext(P.SBP{L0(c), ET(c), DD(c), 0}) == P.btext(L0(c), ET(c), 0, (L0(c) - 0 : U32)) : String},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}) ->
  {P.nolf(c) == True{} : Bool}:
  (h1, h2) = sn
  AB.subst(String, z => {P.nolf(z) == True{} : Bool}, P.srctext(P.SBP{L0(c), ET(c), DD(c), 0}), c, src0_text(c, hv), h1)


# The line end is empty: the piece is the only source.
def ch_empty(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>},
  +he: {String.is_empty(P.pdtext(pd)) == True{} : Bool}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.SB{BTc(c), 0}]), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed})):
  +sp0 = {P.SBP{L0(c), ET(c), DD(c), 0} : P.SrcP}
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok([sp0]), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty([sp0]), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext([sp0])))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    LP.and_le0(D.ok(BTc(c), DD(c)), L0(c), hok),
    DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), he, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, [sp0], pd, False{}, back, wp, None{}, fneed} : S.StP}
  +tx = txt_e(P.srctext(sp0), c, P.pdtext(pd), String.concat(cs), src0_text(c, hv), emp_eq(P.pdtext(pd), he))
  +hl = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(p1, cs), S.intext(p0, c <> cs), tx)
  +hr1 = Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p0), T,
    DS.rep_lines(fa, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, [sp0], pd, False{}, back, wp, None{}, back, wp, None{}, fneed, fneed, hl), hr)
  DS.go_ok2(fa, T, cs, O, N, p1, hb, hw1, hr1, {==}, hg)

# No LF in the piece: it goes to the line end.
def ch_all3(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}, +pp2: P.PdP,
  +e2: {Norm.pend.add(P.mkPd(pd), BTc(c), 0, L0(c)) == P.mkPd(pp2) : Norm.Pd},
  +hpo: {P.pd_ok(pp2) == True{} : Bool},
  +hpt: {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(L0(c), ET(c), 0, L0(c))) : String},
  +hnc: {P.nolf(c) == True{} : Bool}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), BTc(c), 0, L0(c)), False{}, back, PC.mkWin(fa, wp), None{}, fneed})):
  %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), BTc(c), 0, L0(c)), P.mkPd(pp2), e2) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.St{o, S.mkMd(md), Nil{}, _, False{}, back, PC.mkWin(fa, wp), None{}, fneed}))
  +hba = bt_all(c, hok, hv)
  +hn3 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, String.append(P.pdtext(pd), P.btext(L0(c), ET(c), 0, L0(c))), P.pdtext(pp2), Equal.sym(String, P.pdtext(pp2), String.append(P.pdtext(pd), P.btext(L0(c), ET(c), 0, L0(c))), hpt),
    LS.nolf_app(P.pdtext(pd), P.btext(L0(c), ET(c), 0, L0(c)), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
      AB.subst(String, z => {P.nolf(z) == True{} : Bool}, c, P.btext(L0(c), ET(c), 0, L0(c)), Equal.sym(String, P.btext(L0(c), ET(c), 0, L0(c)), c, hba), hnc)))
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pp2), P.nolf(P.pdtext(pp2)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pp2))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pp2)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), {==}, hpo, hn3, {==}, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, Nil{}, pp2, False{}, back, wp, None{}, fneed} : S.StP}
  +tx = txt_a(P.pdtext(pp2), P.pdtext(pd), P.btext(L0(c), ET(c), 0, L0(c)), c, String.concat(cs), hpt, hba)
  +hl = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(p1, cs), S.intext(p0, c <> cs), tx)
  +hr1 = Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p0), T,
    DS.rep_lines(fa, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, Nil{}, pp2, False{}, back, wp, None{}, back, wp, None{}, fneed, fneed, hl), hr)
  DS.go_ok2(fa, T, cs, O, N, p1, hb, hw1, hr1, {==}, hg)

def ch_all2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>},
  +hnc: {P.nolf(c) == True{} : Bool},
  r: &pp2: P.PdP -> ({Norm.pend.add(P.mkPd(pd), C.BT(L0(c), ET(c)), 0, L0(c)) == P.mkPd(pp2) : Norm.Pd}
    & ({P.pd_ok(pp2) == True{} : Bool}
    & {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(L0(c), ET(c), 0, L0(c))) : String}))) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), BTc(c), 0, L0(c)), False{}, back, PC.mkWin(fa, wp), None{}, fneed})):
  (+pp2, r1) = r
  (+e2, r2) = r1
  (hpo, hpt) = r2
  ch_all3(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, pp2, e2, hpo, hpt, hnc)

# The piece's LF at j joins the line end.
def ch_join3(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32, +pp2: P.PdP, +pp0: P.PdP,
  +ej: {Norm.join.k(P.mkPd(pd), BTc(c), j) == (P.mkPd(pp2), BTc(c)) : Norm.Pd & D.Bytes},
  +esrc: {Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(PL.pdsrc(pp2)) : Norm.Src},
  +hso: {P.src_ok(PL.pdsrc(pp2)) == True{} : Bool},
  +hst: {P.srctext(PL.pdsrc(pp2)) == String.append(P.pdtext(pd), P.btext(L0(c), ET(c), 0, (j + 1 : U32))) : String},
  +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp0) : Norm.Pd},
  +hpo0: {P.pd_ok(pp0) == True{} : Bool},
  +hpt0: {P.pdtext(pp0) == "" : String},
  +hlf2: {P.btext(L0(c), ET(c), 0, (j + 1 : U32)) == String.append(P.btext(L0(c), ET(c), 0, j), "\n") : String},
  +hc2: {c == String.append(P.btext(L0(c), ET(c), 0, j), String.append("\n", P.srctext(P.SBP{L0(c), ET(c), DD(c), (j + 1 : U32)}))) : String},
  +hj1: {U32.is_le((j + 1 : U32), L0(c)) == True{} : Bool}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  %Equal.sym(Norm.Pd & D.Bytes, Norm.join.k(P.mkPd(pd), BTc(c), j), (P.mkPd(pp2), BTc(c)), ej) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.join(o, S.mkMd(md), j, _, False{}, back, PC.mkWin(fa, wp), None{}, fneed)))
  %Equal.sym(Norm.Src, Norm.Pd.src(P.mkPd(pp2)), P.mkSrc(PL.pdsrc(pp2)), esrc) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.St{o, S.mkMd(md), [_, Norm.SB{BTc(c), (j + 1 : U32)}], Norm.PB{BY.empty(0n)}, False{}, back, PC.mkWin(fa, wp), None{}, fneed}))
  %Equal.sym(Norm.Pd, Norm.PB{BY.empty(0n)}, P.mkPd(pp0), f1) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.St{o, S.mkMd(md), [P.mkSrc(PL.pdsrc(pp2)), Norm.SB{BTc(c), (j + 1 : U32)}], _, False{}, back, PC.mkWin(fa, wp), None{}, fneed}))
  +sp1 = PL.pdsrc(pp2)
  +sp2 = {P.SBP{L0(c), ET(c), DD(c), (j + 1 : U32)} : P.SrcP}
  +A = P.pdtext(pd)
  +Bq = P.btext(L0(c), ET(c), 0, j)
  +hs1e = AB.subst(String, z => {S.ends_lf(z) == True{} : Bool}, String.append(String.append(A, Bq), "\n"), P.srctext(sp1),
    Equal.trans(String, String.append(String.append(A, Bq), "\n"), String.append(A, String.append(Bq, "\n")), P.srctext(sp1), LS.sassoc(A, Bq, "\n"),
      Equal.sym(String, P.srctext(sp1), String.append(A, String.append(Bq, "\n")),
        Equal.trans(String, P.srctext(sp1), String.append(A, P.btext(L0(c), ET(c), 0, (j + 1 : U32))), String.append(A, String.append(Bq, "\n")), hst,
          Equal.cong(String, String, z => String.append(A, z), P.btext(L0(c), ET(c), 0, (j + 1 : U32)), String.append(Bq, "\n"), hlf2)))),
    DS.ends_lf_lf(String.append(A, Bq)))
  +hsrcs = LP.and_tt(Bool.and(P.src_ok(sp1), S.ends_lf(P.srctext(sp1))), P.src_ok(sp2), LP.and_tt(P.src_ok(sp1), S.ends_lf(P.srctext(sp1)), hso, hs1e),
    LP.and_tt(D.ok(BTc(c), DD(c)), U32.is_le((j + 1 : U32), L0(c)), hok, hj1))
  +hn0 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, "", P.pdtext(pp0), Equal.sym(String, P.pdtext(pp0), "", hpt0), {==})
  +he0 = AB.subst(String, z => {String.is_empty(z) == True{} : Bool}, "", P.pdtext(pp0), Equal.sym(String, P.pdtext(pp0), "", hpt0), {==})
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok([sp1, sp2]), P.pd_ok(pp0), P.nolf(P.pdtext(pp0)), Bool.or(S.src_empty([sp1, sp2]), String.is_empty(P.pdtext(pp0))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pp0)), S.ends_lf(P.srcstext([sp1, sp2])))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hsrcs, hpo0, hn0, he0, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, [sp1, sp2], pp0, False{}, back, wp, None{}, fneed} : S.StP}
  +tx = txt_j(P.srctext(sp1), P.srctext(sp2), P.pdtext(pp0), A, P.btext(L0(c), ET(c), 0, (j + 1 : U32)), Bq, c, String.concat(cs), hst, hlf2, hpt0, hc2)
  +hl = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(p1, cs), S.intext(p0, c <> cs), tx)
  +hr1 = Equal.trans(R.Report, S.report(fa, cs, O, N, p1), S.report(fa, c <> cs, O, N, p0), T,
    DS.rep_lines(fa, c <> cs, cs, O, N, o, md, Nil{}, pd, False{}, [sp1, sp2], pp0, False{}, back, wp, None{}, back, wp, None{}, fneed, fneed, hl), hr)
  DS.go_ok2(fa, T, cs, O, N, p1, hb, hw1, hr1, {==}, hg)

def ch_join2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +hlf2: {P.btext(L0(c), ET(c), 0, (j + 1 : U32)) == String.append(P.btext(L0(c), ET(c), 0, j), "\n") : String},
  +hc2: {c == String.append(P.btext(L0(c), ET(c), 0, j), String.append("\n", P.srctext(P.SBP{L0(c), ET(c), DD(c), (j + 1 : U32)}))) : String},
  +hj1: {U32.is_le((j + 1 : U32), L0(c)) == True{} : Bool},
  r: &pp2: P.PdP -> ({Norm.join.k(P.mkPd(pd), C.BT(L0(c), ET(c)), j) == (P.mkPd(pp2), C.BT(L0(c), ET(c))) : Norm.Pd & D.Bytes}
    & ({Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(PL.pdsrc(pp2)) : Norm.Src}
    & ({P.src_ok(PL.pdsrc(pp2)) == True{} : Bool}
    & {P.srctext(PL.pdsrc(pp2)) == String.append(P.pdtext(pd), P.btext(L0(c), ET(c), 0, (j + 1 : U32))) : String}))),
  pe: &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd}
    & ({P.pd_ok(pp) == True{} : Bool}
    & {P.pdtext(pp) == "" : String}))) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  (+pp2, r1) = r
  (+ej, r2) = r1
  (+esrc, r3) = r2
  (hso, hst) = r3
  (+pp0, pe1) = pe
  (+f1, pe2) = pe1
  (hpo0, hpt0) = pe2
  ch_join3(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, j, pp2, pp0, ej, esrc, hso, hst, f1, hpo0, hpt0, hlf2, hc2, hj1)

def ch_join(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +hk: {Nat.is_lt(U32.to_nat(j), U32.to_nat(L0(c))) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(BTc(c)), U32.to_nat(j)) == Some{10} : Maybe<&2, U32>},
  sl: {P.srctext(P.SBP{L0(c), ET(c), DD(c), 0}) == String.append(P.btext(L0(c), ET(c), 0, (j - 0 : U32)), String.append("\n", P.srctext(P.SBP{L0(c), ET(c), DD(c), (j + 1 : U32)}))) : String}
  & ({P.nolf(P.btext(L0(c), ET(c), 0, (j - 0 : U32))) == True{} : Bool}
  & ({U32.is_le((j + 1 : U32), L0(c)) == True{} : Bool}
  & {E.is_bytes(P.btext(L0(c), ET(c), 0, (j - 0 : U32))) == True{} : Bool}))) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), BTc(c), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  (+h1, s1) = sl
  (+h2, s2) = s1
  (+h3, h4) = s2
  +hn2 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, P.btext(L0(c), ET(c), 0, (j - 0 : U32)), P.btext(L0(c), ET(c), 0, j), bt0(L0(c), ET(c), j), h2)
  +hc2 = Equal.trans(String, c, P.srctext(P.SBP{L0(c), ET(c), DD(c), 0}), String.append(P.btext(L0(c), ET(c), 0, j), String.append("\n", P.srctext(P.SBP{L0(c), ET(c), DD(c), (j + 1 : U32)}))),
    Equal.sym(String, P.srctext(P.SBP{L0(c), ET(c), DD(c), 0}), c, src0_text(c, hv)),
    AB.subst(String, z => {P.srctext(P.SBP{L0(c), ET(c), DD(c), 0}) == String.append(z, String.append("\n", P.srctext(P.SBP{L0(c), ET(c), DD(c), (j + 1 : U32)}))) : String},
      P.btext(L0(c), ET(c), 0, (j - 0 : U32)), P.btext(L0(c), ET(c), 0, j), bt0(L0(c), ET(c), j), h1))
  ch_join2(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, j, LP.bt_lf(L0(c), ET(c), DD(c), j, hok, hk, hlf), hc2, h3,
    PL.join_ok(pd, L0(c), ET(c), DD(c), j, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hok, hk, hlf, DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hn2),
    PL.pd_empty())

# After the piece's first LF search.
def ch_z(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32, +z: Bool,
  +ez: {U32.is_eq(j, L0(c)) == z : Bool},
  +hf: {U32.to_nat(j) == D.first(D.view(BTc(c)), U32.to_nat(0), U32.to_nat(L0(c)), 10) : Nat}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.lf(z, o, S.mkMd(md), BTc(c), j, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  match z:
    case True{}:
      +V = D.view(BTc(c))
      +nL = U32.to_nat(L0(c))
      +hlen = Equal.sym(Nat, List.length(&2, U32, V), nL, O.view_size_t(L0(c), ET(c), DD(c), hok))
      +ht = AB.subst(Nat, w => {Nat.is_le(nL, w) == True{} : Bool}, nL, List.length(&2, U32, V), hlen, N.le_refl(nL))
      +ejL = U.is_eq_true(j, L0(c), ez)
      +hfL = AB.subst(U32, w => {U32.to_nat(w) == D.first(V, U32.to_nat(0), nL, 10) : Nat}, j, L0(c), ejL, hf)
      sn = PL.src_nolf(L0(c), ET(c), DD(c), 0, hok, LP.u32_le0(L0(c)), Equal.sym(Nat, nL, D.first(V, U32.to_nat(0), nL, 10), hfL))
      ch_all2(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, ch_nolf(c, sn, hv), PL.pend_add(pd, L0(c), ET(c), DD(c), 0, L0(c), DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hok, N.le_refl(nL)))
    case False{}:
      +V = D.view(BTc(c))
      +nL = U32.to_nat(L0(c))
      +hlen = Equal.sym(Nat, List.length(&2, U32, V), nL, O.view_size_t(L0(c), ET(c), DD(c), hok))
      +ht = AB.subst(Nat, w => {Nat.is_le(nL, w) == True{} : Bool}, nL, List.length(&2, U32, V), hlen, N.le_refl(nL))
      +hr0 = Q.first_range(V, U32.to_nat(0), nL, 10, N.le_zero_l(nL), ht)
      +hjl = AB.subst(Nat, w => {Nat.is_le(w, nL) == True{} : Bool}, D.first(V, U32.to_nat(0), nL, 10), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf),
        AB.and_true_r(Nat.is_le(U32.to_nat(0), D.first(V, U32.to_nat(0), nL, 10)), Nat.is_le(D.first(V, U32.to_nat(0), nL, 10), nL), hr0))
      +hne = Equal.trans(Bool, Nat.is_eq(U32.to_nat(j), nL), U32.is_eq(j, L0(c)), False{}, Equal.sym(Bool, U32.is_eq(j, L0(c)), Nat.is_eq(U32.to_nat(j), nL), U.is_eq_to_nat(j, L0(c))), ez)
      +hk = Equal.trans(Bool, Nat.is_lt(U32.to_nat(j), nL), Nat.is_le(1n+U32.to_nat(j), nL), True{}, Equal.sym(Bool, Nat.is_le(1n+U32.to_nat(j), nL), Nat.is_lt(U32.to_nat(j), nL), N.le_succ_lt(U32.to_nat(j), nL)),
        N.le_ne(U32.to_nat(j), nL, hjl, hne))
      +hfl = AB.subst(Nat, w => {Nat.is_lt(w, nL) == True{} : Bool}, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf, hk)
      +hhit = AB.subst(Nat, w => {D.has(V, w, 10) == True{} : Bool}, D.first(V, U32.to_nat(0), nL, 10), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf),
        Q.first_hit(V, U32.to_nat(0), nL, 10, N.le_zero_l(nL), ht, hfl))
      +hlf = LT.has_get(List.get(&2, U32, V, U32.to_nat(j)), 10, hhit)
      ch_join(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, j, hk, hlf, PL.src_line(L0(c), ET(c), DD(c), 0, j, hok, LP.u32_le0(L0(c)), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf), hk))

def ch_lf2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +e1: {NF.lf(BTc(c), 0) == NF.Tb{BTc(c), j, U32.is_eq(j, L0(c)), False{}} : NF.Tb},
  +hf: {U32.to_nat(j) == D.first(D.view(BTc(c)), U32.to_nat(0), U32.to_nat(L0(c)), 10) : Nat}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.find(o, S.mkMd(md), NF.lf(BTc(c), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  %Equal.sym(NF.Tb, NF.lf(BTc(c), 0), NF.Tb{BTc(c), j, U32.is_eq(j, L0(c)), False{}}, e1) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.find(o, S.mkMd(md), _, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)))
  ch_z(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, j, U32.is_eq(j, L0(c)), {==}, hf)

def ch_lf(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>},
  r: &j: U32 -> ({NF.lf(C.BT(L0(c), ET(c)), 0) == NF.Tb{C.BT(L0(c), ET(c)), j, U32.is_eq(j, L0(c)), False{}} : NF.Tb}
    & {PL.n(j) == D.first(PL.xs(L0(c), ET(c)), PL.n(0), PL.n(L0(c)), 10) : Nat})) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.find(o, S.mkMd(md), NF.lf(BTc(c), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  (+j, r1) = r
  (e1, hf) = r1
  ch_lf2(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, j, e1, hf)

def core_if(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}, +z: Bool,
  +ez: {Nat.is_eq(String.length(P.pdtext(pd)), 0n) == z : Bool}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.if(z, o, S.mkMd(md), Nil{}, BTc(c), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  match z:
    case True{}:
      ch_empty(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, DS.empty_of_len(P.pdtext(pd), ez))
    case False{}:
      ch_lf(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, PL.lf_ok(L0(c), ET(c), DD(c), 0, hok, LP.u32_le0(L0(c))))

def core(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(BTc(c), DD(c)) == True{} : Bool},
  +hv: {D.view(BTc(c)) == E.codes(c) : List<&2, U32>}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  %Equal.sym(Norm.Pd & Nat, Norm.Pd.len(P.mkPd(pd)), (P.mkPd(pd), String.length(P.pdtext(pd))), PL.pd_len(pd, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(L0(c), EN.enc_t(c)), _, False{}, back, PC.mkWin(fa, wp), None{}, fneed)))
  core_if(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, Nat.is_eq(String.length(P.pdtext(pd)), 0n), {==})

# The run gets room for the piece
# ===============================

def chunk_mb2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>},
  +e: {NR.reserve(P.mkRun(rp), L0(c)) == P.mkRun(rp2) : NR.Run},
  +hi2: {RN.RunInv(rp2) == True{} : Bool},
  +hs: {P.specRun(rp2) == P.specRun(rp) : R.RunSt}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), L0(c))}, Nil{}, C.BT(L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
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
  %Equal.sym(NR.Run, NR.reserve(P.mkRun(rp), L0(c)), P.mkRun(rp2), e) :
    DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed)))
  core(fa, T, c, cs, O, N, o, md2, pd, back, wp, fneed, hb, hw2, hr2, hg2, hok, hv)

def chunk_mb(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>},
  r: &p2: P.RunP -> ({NR.reserve(P.mkRun(rp), L0(c)) == P.mkRun(p2) : NR.Run}
    & ({RN.RunInv(p2) == True{} : Bool}
    & ({P.specRun(p2) == P.specRun(rp) : R.RunSt}
    & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32})))) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), L0(c))}, Nil{}, C.BT(L0(c), EN.enc_t(c)), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed))):
  (+rp2, r1) = r
  (+e, r2) = r1
  (+hi2, r3) = r2
  (hs, ho) = r3
  chunk_mb2(fa, T, c, cs, O, N, o, rp, rp2, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv, e, hi2, hs)

# By the run's mode (the String mode's run has no buffer).
def chunk_md(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Pr.Chunk{C.BT(L0(c), EN.enc_t(c))})):
  match md:
    case S.MBP{+rp}:
      chunk_mb(fa, T, c, cs, O, N, o, rp, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv,
        RN.run_reserve(rp, L0(c), DO.x8_a(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), E.all_bytes(S.opts_args(o)), hw)))
    case S.MSP{+s, +qs, +ql, +code}:
      core(fa, T, c, cs, O, N, o, S.MSP{s, qs, ql, code}, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv)

# The piece's facts from the enc area.
def chunk_enc(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  r: {D.ok(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), Pr.Chunk{C.BT(L0(c), EN.enc_t(c))})):
  (hok, r1) = r
  (hv, r2) = r1
  chunk_md(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, hok, hv)

# step_chunk with the eof flag (DO.StepG2; every state here is before the
# end of the file), for the assembly's sg_chunk.
def step_chunk_h2(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})):
  match p:
    case S.StP{+o, +md, Con{+x, +t}, +pd, +eof, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Con{x, t}, pd, eof, back, wp, asked, fneed} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, q), Pr.Chunk{E.enc(c)})),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, q), Pr.Chunk{E.enc(c)})),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed} : S.StP}
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, q), Pr.Chunk{E.enc(c)})),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
      +hw = DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm)
      %Equal.sym(D.Bytes, E.enc(c), C.BT(L0(c), EN.enc_t(c)), EN.enc_bt(c)) :
        DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, q), Pr.Chunk{_}))
      chunk_enc(fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, hb, hw, hr, hg, EN.enc_ok(c, hcb, hcn))

# step_chunk, as proof_b_drive.bend states it.
def step_chunk_h(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DR.StepG(fa, T, cs, O, N, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})):
  DO.sg2w(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}), step_chunk_h2(fa, T, c, cs, O, N, p, hb, hm, hr, hcb, hcn, hg))
