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
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_b_drive_chunk.bend as DC
import ./proof_b_lines.bend as PL
import ./proof_b_lines_str.bend as LS
import ./proof_b_lines_pd.bend as LP
import ./proof_b_lines_lst.bend as LT
import ./proof_base.bend as PB
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_find.bend as FD
import ../lawful-bytes/proof_list.bend as Q
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-bytes/proof_grow.bend as G
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Phase E, area "qif": norm.bend's feed (after the room in the output buffer)
# for a piece given as any good buffer C.BT(len, t) of depth d whose view is
# E.codes(c). This is proof_b_drive_chunk.bend's core with its BTc(c) =
# E.enc(c) replaced by that buffer; its conclusion is the fed state itself
# (Fed) instead of the step after it, so W.feed_line (feed without the room)
# uses it too. Its leaves were made from phase B's by a small script (BTc(c)
# to C.BT(len, t), the depth to d, StepG2 to Fed); edit them directly.

# What the feed gives from a state p waiting for more: a good state p1 with
# the same run and options, nothing asked, not at the end of the file, and c
# moved in front of the pieces still to come.
def Fed(+fa: List<&2, B.Contig>, +c: String, +p: S.StP, X: Norm.St) -> Type:
  &p1: S.StP -> ({X == S.mkSt(fa, p1) : Norm.St}
    & ({S.WF(fa, p1) == True{} : Bool} & ({S.StP.md(p1) == S.StP.md(p) : S.MdP} & ({S.StP.o(p1) == S.StP.o(p) : B.Opts}
    & ({S.StP.asked(p1) == None{} : Maybe<&2, List<&2, Pr.Req>>} & ({S.StP.eof(p1) == False{} : Bool}
    & (@cs: List<&2, String> -> {S.intext(p1, cs) == S.intext(p, c <> cs) : String})))))))

# The piece as a mirror
# =====================

# The text of the piece's buffer is the piece.
def piece_text(+c: String, +len: U32, +t: AT.Tree<U32>, +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  {NR.chars(D.view(C.BT(len, t))) == c : String}:
  %Equal.sym(List<&2, U32>, D.view(C.BT(len, t)), E.codes(c), hv) : {NR.chars(_) == c : String}
  LS.chars_codes(c)

# The piece read from 0 is the piece.
def src0_text(+c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  {P.srctext(P.SBP{len, t, d, 0}) == c : String}:
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, D.view(C.BT(len, t)), 0n), D.view(C.BT(len, t)), FD.drop_zero(D.view(C.BT(len, t)))) : {NR.chars(_) == c : String}
  piece_text(c, len, t, hv)

# All of the piece's bytes are the piece.
def bt_all(+c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  {P.btext(len, t, 0, len) == c : String}:
  +V = D.view(C.BT(len, t))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, FD.drop_zero(V)) : {NR.chars(List.take(&2, U32, _, U32.to_nat(len))) == c : String}
  %O.view_size_t(len, t, d, hok) : {NR.chars(List.take(&2, U32, V, _)) == c : String}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, V, List.length(&2, U32, V)), V, G.take_all(V)) : {NR.chars(_) == c : String}
  piece_text(c, len, t, hv)

# The core: after the room, by the line end's length
# ==================================================

# The piece has no LF when its first LF is its end.
def ch_nolf(+c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  sn: {P.nolf(P.srctext(P.SBP{len, t, d, 0})) == True{} : Bool}
  & {P.srctext(P.SBP{len, t, d, 0}) == P.btext(len, t, 0, (len - 0 : U32)) : String},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  {P.nolf(c) == True{} : Bool}:
  (h1, h2) = sn
  AB.subst(String, z => {P.nolf(z) == True{} : Bool}, P.srctext(P.SBP{len, t, d, 0}), c, src0_text(c, len, t, d, hv), h1)


# The line end is empty: the piece is the only source.
def ch_empty(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +he: {String.is_empty(P.pdtext(pd)) == True{} : Bool}) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.St{o, S.mkMd(md), List.append(&1, Norm.Src, Nil{}, [Norm.SB{C.BT(len, t), 0}]), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed}):
  +sp0 = {P.SBP{len, t, d, 0} : P.SrcP}
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok([sp0]), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty([sp0]), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext([sp0])))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
    LP.and_le0(D.ok(C.BT(len, t), d), len, hok),
    DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), he, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, [sp0], pd, False{}, back, wp, None{}, fneed} : S.StP}
  (p1, ({==}, (hw1, ({==}, ({==}, ({==}, ({==}, cs => DC.txt_e(P.srctext(sp0), c, P.pdtext(pd), String.concat(cs), src0_text(c, len, t, d, hv), DC.emp_eq(P.pdtext(pd), he)))))))))

# No LF in the piece: it goes to the line end.
def ch_all3(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, +pp2: P.PdP,
  +e2: {Norm.pend.add(P.mkPd(pd), C.BT(len, t), 0, len) == P.mkPd(pp2) : Norm.Pd},
  +hpo: {P.pd_ok(pp2) == True{} : Bool},
  +hpt: {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(len, t, 0, len)) : String},
  +hnc: {P.nolf(c) == True{} : Bool}) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), C.BT(len, t), 0, len), False{}, back, PC.mkWin(fa, wp), None{}, fneed}):
  %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), C.BT(len, t), 0, len), P.mkPd(pp2), e2) :
    Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.St{o, S.mkMd(md), Nil{}, _, False{}, back, PC.mkWin(fa, wp), None{}, fneed})
  +hba = bt_all(c, len, t, d, hok, hv)
  +hn3 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, String.append(P.pdtext(pd), P.btext(len, t, 0, len)), P.pdtext(pp2), Equal.sym(String, P.pdtext(pp2), String.append(P.pdtext(pd), P.btext(len, t, 0, len)), hpt),
    LS.nolf_app(P.pdtext(pd), P.btext(len, t, 0, len), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw),
      AB.subst(String, z => {P.nolf(z) == True{} : Bool}, c, P.btext(len, t, 0, len), Equal.sym(String, P.btext(len, t, 0, len), c, hba), hnc)))
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pp2), P.nolf(P.pdtext(pp2)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pp2))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pp2)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), {==}, hpo, hn3, {==}, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, Nil{}, pp2, False{}, back, wp, None{}, fneed} : S.StP}
  (p1, ({==}, (hw1, ({==}, ({==}, ({==}, ({==}, cs => DC.txt_a(P.pdtext(pp2), P.pdtext(pd), P.btext(len, t, 0, len), c, String.concat(cs), hpt, hba))))))))

def ch_all2(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +hnc: {P.nolf(c) == True{} : Bool},
  r: &pp2: P.PdP -> ({Norm.pend.add(P.mkPd(pd), C.BT(len, t), 0, len) == P.mkPd(pp2) : Norm.Pd}
    & ({P.pd_ok(pp2) == True{} : Bool}
    & {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(len, t, 0, len)) : String}))) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.St{o, S.mkMd(md), Nil{}, Norm.pend.add(P.mkPd(pd), C.BT(len, t), 0, len), False{}, back, PC.mkWin(fa, wp), None{}, fneed}):
  (+pp2, r1) = r
  (+e2, r2) = r1
  (hpo, hpt) = r2
  ch_all3(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, pp2, e2, hpo, hpt, hnc)

# The piece's LF at j joins the line end.
def ch_join3(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, +j: U32, +pp2: P.PdP, +pp0: P.PdP,
  +ej: {Norm.join.k(P.mkPd(pd), C.BT(len, t), j) == (P.mkPd(pp2), C.BT(len, t)) : Norm.Pd & D.Bytes},
  +esrc: {Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(PL.pdsrc(pp2)) : Norm.Src},
  +hso: {P.src_ok(PL.pdsrc(pp2)) == True{} : Bool},
  +hst: {P.srctext(PL.pdsrc(pp2)) == String.append(P.pdtext(pd), P.btext(len, t, 0, (j + 1 : U32))) : String},
  +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp0) : Norm.Pd},
  +hpo0: {P.pd_ok(pp0) == True{} : Bool},
  +hpt0: {P.pdtext(pp0) == "" : String},
  +hlf2: {P.btext(len, t, 0, (j + 1 : U32)) == String.append(P.btext(len, t, 0, j), "\n") : String},
  +hc2: {c == String.append(P.btext(len, t, 0, j), String.append("\n", P.srctext(P.SBP{len, t, d, (j + 1 : U32)}))) : String},
  +hj1: {U32.is_le((j + 1 : U32), len) == True{} : Bool}) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), C.BT(len, t), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  %Equal.sym(Norm.Pd & D.Bytes, Norm.join.k(P.mkPd(pd), C.BT(len, t), j), (P.mkPd(pp2), C.BT(len, t)), ej) :
    Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.join(o, S.mkMd(md), j, _, False{}, back, PC.mkWin(fa, wp), None{}, fneed))
  %Equal.sym(Norm.Src, Norm.Pd.src(P.mkPd(pp2)), P.mkSrc(PL.pdsrc(pp2)), esrc) :
    Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.St{o, S.mkMd(md), [_, Norm.SB{C.BT(len, t), (j + 1 : U32)}], Norm.PB{BY.empty(0n)}, False{}, back, PC.mkWin(fa, wp), None{}, fneed})
  %Equal.sym(Norm.Pd, Norm.PB{BY.empty(0n)}, P.mkPd(pp0), f1) :
    Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.St{o, S.mkMd(md), [P.mkSrc(PL.pdsrc(pp2)), Norm.SB{C.BT(len, t), (j + 1 : U32)}], _, False{}, back, PC.mkWin(fa, wp), None{}, fneed})
  +sp1 = PL.pdsrc(pp2)
  +sp2 = {P.SBP{len, t, d, (j + 1 : U32)} : P.SrcP}
  +A = P.pdtext(pd)
  +Bq = P.btext(len, t, 0, j)
  +hs1e = AB.subst(String, z => {S.ends_lf(z) == True{} : Bool}, String.append(String.append(A, Bq), "\n"), P.srctext(sp1),
    Equal.trans(String, String.append(String.append(A, Bq), "\n"), String.append(A, String.append(Bq, "\n")), P.srctext(sp1), LS.sassoc(A, Bq, "\n"),
      Equal.sym(String, P.srctext(sp1), String.append(A, String.append(Bq, "\n")),
        Equal.trans(String, P.srctext(sp1), String.append(A, P.btext(len, t, 0, (j + 1 : U32))), String.append(A, String.append(Bq, "\n")), hst,
          Equal.cong(String, String, z => String.append(A, z), P.btext(len, t, 0, (j + 1 : U32)), String.append(Bq, "\n"), hlf2)))),
    DS.ends_lf_lf(String.append(A, Bq)))
  +hsrcs = LP.and_tt(Bool.and(P.src_ok(sp1), S.ends_lf(P.srctext(sp1))), P.src_ok(sp2), LP.and_tt(P.src_ok(sp1), S.ends_lf(P.srctext(sp1)), hso, hs1e),
    LP.and_tt(D.ok(C.BT(len, t), d), U32.is_le((j + 1 : U32), len), hok, hj1))
  +hn0 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, "", P.pdtext(pp0), Equal.sym(String, P.pdtext(pp0), "", hpt0), {==})
  +he0 = AB.subst(String, z => {String.is_empty(z) == True{} : Bool}, "", P.pdtext(pp0), Equal.sym(String, P.pdtext(pp0), "", hpt0), {==})
  +hw1 = DO.x9_mk(S.md_ok(md), S.srcs_ok([sp1, sp2]), P.pd_ok(pp0), P.nolf(P.pdtext(pp0)), Bool.or(S.src_empty([sp1, sp2]), String.is_empty(P.pdtext(pp0))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pp0)), S.ends_lf(P.srcstext([sp1, sp2])))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), DO.x8_a(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hsrcs, hpo0, hn0, he0, {==},
    DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))
  +p0 = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
  +p1 = {S.StP{o, md, [sp1, sp2], pp0, False{}, back, wp, None{}, fneed} : S.StP}
  (p1, ({==}, (hw1, ({==}, ({==}, ({==}, ({==}, cs => DC.txt_j(P.srctext(sp1), P.srctext(sp2), P.pdtext(pp0), A, P.btext(len, t, 0, (j + 1 : U32)), Bq, c, String.concat(cs), hst, hlf2, hpt0, hc2))))))))

def ch_join2(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +hlf2: {P.btext(len, t, 0, (j + 1 : U32)) == String.append(P.btext(len, t, 0, j), "\n") : String},
  +hc2: {c == String.append(P.btext(len, t, 0, j), String.append("\n", P.srctext(P.SBP{len, t, d, (j + 1 : U32)}))) : String},
  +hj1: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  r: &pp2: P.PdP -> ({Norm.join.k(P.mkPd(pd), C.BT(len, t), j) == (P.mkPd(pp2), C.BT(len, t)) : Norm.Pd & D.Bytes}
    & ({Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(PL.pdsrc(pp2)) : Norm.Src}
    & ({P.src_ok(PL.pdsrc(pp2)) == True{} : Bool}
    & {P.srctext(PL.pdsrc(pp2)) == String.append(P.pdtext(pd), P.btext(len, t, 0, (j + 1 : U32))) : String}))),
  pe: &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd}
    & ({P.pd_ok(pp) == True{} : Bool}
    & {P.pdtext(pp) == "" : String}))) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), C.BT(len, t), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  (+pp2, r1) = r
  (+ej, r2) = r1
  (+esrc, r3) = r2
  (hso, hst) = r3
  (+pp0, pe1) = pe
  (+f1, pe2) = pe1
  (hpo0, hpt0) = pe2
  ch_join3(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, j, pp2, pp0, ej, esrc, hso, hst, f1, hpo0, hpt0, hlf2, hc2, hj1)

def ch_join(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +hk: {Nat.is_lt(U32.to_nat(j), U32.to_nat(len)) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(C.BT(len, t)), U32.to_nat(j)) == Some{10} : Maybe<&2, U32>},
  sl: {P.srctext(P.SBP{len, t, d, 0}) == String.append(P.btext(len, t, 0, (j - 0 : U32)), String.append("\n", P.srctext(P.SBP{len, t, d, (j + 1 : U32)}))) : String}
  & ({P.nolf(P.btext(len, t, 0, (j - 0 : U32))) == True{} : Bool}
  & ({U32.is_le((j + 1 : U32), len) == True{} : Bool}
  & {E.is_bytes(P.btext(len, t, 0, (j - 0 : U32))) == True{} : Bool}))) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.join(o, S.mkMd(md), j, Norm.join.k(P.mkPd(pd), C.BT(len, t), j), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  (+h1, s1) = sl
  (+h2, s2) = s1
  (+h3, h4) = s2
  +hn2 = AB.subst(String, z => {P.nolf(z) == True{} : Bool}, P.btext(len, t, 0, (j - 0 : U32)), P.btext(len, t, 0, j), DC.bt0(len, t, j), h2)
  +hc2 = Equal.trans(String, c, P.srctext(P.SBP{len, t, d, 0}), String.append(P.btext(len, t, 0, j), String.append("\n", P.srctext(P.SBP{len, t, d, (j + 1 : U32)}))),
    Equal.sym(String, P.srctext(P.SBP{len, t, d, 0}), c, src0_text(c, len, t, d, hv)),
    AB.subst(String, z => {P.srctext(P.SBP{len, t, d, 0}) == String.append(z, String.append("\n", P.srctext(P.SBP{len, t, d, (j + 1 : U32)}))) : String},
      P.btext(len, t, 0, (j - 0 : U32)), P.btext(len, t, 0, j), DC.bt0(len, t, j), h1))
  ch_join2(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, j, LP.bt_lf(len, t, d, j, hok, hk, hlf), hc2, h3,
    PL.join_ok(pd, len, t, d, j, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hok, hk, hlf, DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hn2),
    PL.pd_empty())

# After the piece's first LF search.
def ch_z(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, +j: U32, +z: Bool,
  +ez: {U32.is_eq(j, len) == z : Bool},
  +hf: {U32.to_nat(j) == D.first(D.view(C.BT(len, t)), U32.to_nat(0), U32.to_nat(len), 10) : Nat}) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.lf(z, o, S.mkMd(md), C.BT(len, t), j, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  match z:
    case True{}:
      +V = D.view(C.BT(len, t))
      +nL = U32.to_nat(len)
      +hlen = Equal.sym(Nat, List.length(&2, U32, V), nL, O.view_size_t(len, t, d, hok))
      +ht = AB.subst(Nat, w => {Nat.is_le(nL, w) == True{} : Bool}, nL, List.length(&2, U32, V), hlen, N.le_refl(nL))
      +ejL = U.is_eq_true(j, len, ez)
      +hfL = AB.subst(U32, w => {U32.to_nat(w) == D.first(V, U32.to_nat(0), nL, 10) : Nat}, j, len, ejL, hf)
      sn = PL.src_nolf(len, t, d, 0, hok, LP.u32_le0(len), Equal.sym(Nat, nL, D.first(V, U32.to_nat(0), nL, 10), hfL))
      ch_all2(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, ch_nolf(c, len, t, d, sn, hv), PL.pend_add(pd, len, t, d, 0, len, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw), hok, N.le_refl(nL)))
    case False{}:
      +V = D.view(C.BT(len, t))
      +nL = U32.to_nat(len)
      +hlen = Equal.sym(Nat, List.length(&2, U32, V), nL, O.view_size_t(len, t, d, hok))
      +ht = AB.subst(Nat, w => {Nat.is_le(nL, w) == True{} : Bool}, nL, List.length(&2, U32, V), hlen, N.le_refl(nL))
      +hr0 = Q.first_range(V, U32.to_nat(0), nL, 10, N.le_zero_l(nL), ht)
      +hjl = AB.subst(Nat, w => {Nat.is_le(w, nL) == True{} : Bool}, D.first(V, U32.to_nat(0), nL, 10), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf),
        AB.and_true_r(Nat.is_le(U32.to_nat(0), D.first(V, U32.to_nat(0), nL, 10)), Nat.is_le(D.first(V, U32.to_nat(0), nL, 10), nL), hr0))
      +hne = Equal.trans(Bool, Nat.is_eq(U32.to_nat(j), nL), U32.is_eq(j, len), False{}, Equal.sym(Bool, U32.is_eq(j, len), Nat.is_eq(U32.to_nat(j), nL), U.is_eq_to_nat(j, len)), ez)
      +hk = Equal.trans(Bool, Nat.is_lt(U32.to_nat(j), nL), Nat.is_le(1n+U32.to_nat(j), nL), True{}, Equal.sym(Bool, Nat.is_le(1n+U32.to_nat(j), nL), Nat.is_lt(U32.to_nat(j), nL), N.le_succ_lt(U32.to_nat(j), nL)),
        N.le_ne(U32.to_nat(j), nL, hjl, hne))
      +hfl = AB.subst(Nat, w => {Nat.is_lt(w, nL) == True{} : Bool}, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf, hk)
      +hhit = AB.subst(Nat, w => {D.has(V, w, 10) == True{} : Bool}, D.first(V, U32.to_nat(0), nL, 10), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf),
        Q.first_hit(V, U32.to_nat(0), nL, 10, N.le_zero_l(nL), ht, hfl))
      +hlf = LT.has_get(List.get(&2, U32, V, U32.to_nat(j)), 10, hhit)
      ch_join(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, j, hk, hlf, PL.src_line(len, t, d, 0, j, hok, LP.u32_le0(len), Equal.sym(Nat, U32.to_nat(j), D.first(V, U32.to_nat(0), nL, 10), hf), hk))

def ch_lf2(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, +j: U32,
  +e1: {NF.lf(C.BT(len, t), 0) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb},
  +hf: {U32.to_nat(j) == D.first(D.view(C.BT(len, t)), U32.to_nat(0), U32.to_nat(len), 10) : Nat}) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.find(o, S.mkMd(md), NF.lf(C.BT(len, t), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), 0), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, e1) :
    Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.find(o, S.mkMd(md), _, P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed))
  ch_z(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, j, U32.is_eq(j, len), {==}, hf)

def ch_lf(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  r: &j: U32 -> ({NF.lf(C.BT(len, t), 0) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb}
    & {PL.n(j) == D.first(PL.xs(len, t), PL.n(0), PL.n(len), 10) : Nat})) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.find(o, S.mkMd(md), NF.lf(C.BT(len, t), 0), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  (+j, r1) = r
  (e1, hf) = r1
  ch_lf2(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, j, e1, hf)

def core_if(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, +z: Bool,
  +ez: {Nat.is_eq(String.length(P.pdtext(pd)), 0n) == z : Bool}) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.if(z, o, S.mkMd(md), Nil{}, C.BT(len, t), P.mkPd(pd), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  match z:
    case True{}:
      ch_empty(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, DS.empty_of_len(P.pdtext(pd), ez))
    case False{}:
      ch_lf(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, PL.lf_ok(len, t, d, 0, hok, LP.u32_le0(len)))

def core(+fa: List<&2, B.Contig>, +c: String, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed)):
  %Equal.sym(Norm.Pd & Nat, Norm.Pd.len(P.mkPd(pd)), (P.mkPd(pd), String.length(P.pdtext(pd))), PL.pd_len(pd, DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw))) :
    Fed(fa, c, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(len, t), _, False{}, back, PC.mkWin(fa, wp), None{}, fneed))
  core_if(fa, c, len, t, d, o, md, pd, back, wp, fneed, hw, hok, hv, Nat.is_eq(String.length(P.pdtext(pd)), 0n), {==})